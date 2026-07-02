use std::sync::Arc;

use tokio::sync::{Mutex, mpsc};
use tower_lsp::lsp_types as lsp;

use crate::cache::LspCache;
use crate::completion::completion_items_for_source_with_module_paths;
use crate::navigation::{SourceDocument, definition_for_documents, hover_for_documents};
use crate::project::project_context_for_uri;
use crate::text::apply_content_changes;

#[derive(Debug, Clone)]
struct CheckJob {
    uri: lsp::Url,
    text: String,
    version: Option<i32>,
}

#[tower_lsp::async_trait]
pub trait DiagnosticPublisher: Clone + Send + Sync + 'static {
    async fn publish_diagnostics(
        &self,
        uri: lsp::Url,
        diagnostics: Vec<lsp::Diagnostic>,
        version: Option<i32>,
    );
}

pub struct DiagnosticService<P>
where
    P: DiagnosticPublisher,
{
    cache: Arc<Mutex<LspCache>>,
    publisher: P,
    full_check_tx: mpsc::Sender<CheckJob>,
}

impl<P> DiagnosticService<P>
where
    P: DiagnosticPublisher,
{
    pub fn new(publisher: P) -> Self {
        let cache = Arc::new(Mutex::new(LspCache::new()));
        let (full_check_tx, mut full_check_rx) = mpsc::channel::<CheckJob>(32);
        let worker_cache = Arc::clone(&cache);
        let worker_publisher = publisher.clone();
        let worker_tx = full_check_tx.clone();

        tokio::spawn(async move {
            while let Some(job) = full_check_rx.recv().await {
                let is_current = {
                    let cache = worker_cache.lock().await;
                    cache.version(&job.uri) == job.version
                        && cache.text(&job.uri).is_some_and(|text| text == job.text)
                };
                if !is_current {
                    continue;
                }

                let update = {
                    let mut cache = worker_cache.lock().await;
                    cache.update_full(job.uri.clone(), job.version, job.text.clone())
                };
                worker_publisher
                    .publish_diagnostics(job.uri.clone(), update.diagnostics, job.version)
                    .await;
                for dependent in update.dirty_dependents {
                    let snapshot = {
                        let cache = worker_cache.lock().await;
                        cache.text(&dependent).map(|text| {
                            let version = cache.version(&dependent);
                            (text, version)
                        })
                    };
                    if let Some((text, version)) = snapshot {
                        let _ = worker_tx
                            .send(CheckJob {
                                uri: dependent,
                                text,
                                version,
                            })
                            .await;
                    }
                }
            }
        });

        Self {
            cache,
            publisher,
            full_check_tx,
        }
    }

    pub async fn did_open(&self, uri: lsp::Url, version: Option<i32>, text: String) {
        self.update_document(uri, version, text).await;
    }

    pub async fn did_change(
        &self,
        uri: lsp::Url,
        version: Option<i32>,
        changes: Vec<lsp::TextDocumentContentChangeEvent>,
    ) {
        let text = {
            let cache = self.cache.lock().await;
            cache.text(&uri).unwrap_or_default()
        };
        let text = apply_content_changes(text, changes);
        self.update_document(uri, version, text).await;
    }

    pub async fn did_close(&self, uri: lsp::Url) {
        {
            let mut cache = self.cache.lock().await;
            cache.remove(&uri);
        }
        self.publisher
            .publish_diagnostics(uri, Vec::new(), None)
            .await;
    }

    pub async fn completion(
        &self,
        uri: &lsp::Url,
        position: lsp::Position,
    ) -> Vec<lsp::CompletionItem> {
        let text = {
            let cache = self.cache.lock().await;
            cache.text(uri)
        };
        let Some(text) = text else {
            return Vec::new();
        };
        let extra_module_paths = project_context_for_uri(uri)
            .map(|project| {
                let current = project.module_key_for_uri(uri);
                project.completion_module_paths(&current)
            })
            .unwrap_or_default();
        completion_items_for_source_with_module_paths(&text, position, extra_module_paths)
    }

    pub async fn goto_definition(
        &self,
        uri: &lsp::Url,
        position: lsp::Position,
    ) -> Option<lsp::GotoDefinitionResponse> {
        let documents = self.document_snapshots().await;
        definition_for_documents(&documents, uri, position)
    }

    pub async fn hover(&self, uri: &lsp::Url, position: lsp::Position) -> Option<lsp::Hover> {
        let documents = self.document_snapshots().await;
        hover_for_documents(&documents, uri, position)
    }

    pub async fn semantic_tokens(&self, uri: &lsp::Url) -> Option<lsp::SemanticTokensResult> {
        let tokens = {
            let cache = self.cache.lock().await;
            cache.semantic_tokens(uri)
        }?;
        Some(lsp::SemanticTokensResult::Tokens(lsp::SemanticTokens {
            result_id: None,
            data: tokens,
        }))
    }

    async fn update_document(&self, uri: lsp::Url, version: Option<i32>, text: String) {
        let update = {
            let mut cache = self.cache.lock().await;
            cache.update_fast(uri.clone(), version, text.clone())
        };
        self.publisher
            .publish_diagnostics(uri.clone(), update.diagnostics, version)
            .await;

        let _ = self
            .full_check_tx
            .send(CheckJob {
                uri: uri.clone(),
                text,
                version,
            })
            .await;
        self.load_dependency_files(&[uri]).await;
    }

    async fn document_snapshots(&self) -> Vec<SourceDocument> {
        let cache = self.cache.lock().await;
        cache.document_snapshots()
    }

    async fn load_dependency_files(&self, roots: &[lsp::Url]) {
        let candidates = {
            let cache = self.cache.lock().await;
            roots
                .iter()
                .flat_map(|uri| cache.dependency_file_candidates(uri))
                .collect::<Vec<_>>()
        };
        for dependency in candidates {
            let Ok(path) = dependency.to_file_path() else {
                continue;
            };
            let Ok(text) = std::fs::read_to_string(path) else {
                continue;
            };
            {
                let mut cache = self.cache.lock().await;
                cache.update_fast(dependency.clone(), None, text.clone());
            }
            let _ = self
                .full_check_tx
                .send(CheckJob {
                    uri: dependency,
                    text,
                    version: None,
                })
                .await;
        }
    }
}
