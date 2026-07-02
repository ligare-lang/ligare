use tower_lsp::lsp_types as lsp;
use tower_lsp::{Client, LanguageServer};

use crate::{DiagnosticPublisher, DiagnosticService, semantic_tokens_legend};

#[derive(Clone)]
struct TowerDiagnosticPublisher {
    client: Client,
}

#[tower_lsp::async_trait]
impl DiagnosticPublisher for TowerDiagnosticPublisher {
    async fn publish_diagnostics(
        &self,
        uri: lsp::Url,
        diagnostics: Vec<lsp::Diagnostic>,
        version: Option<i32>,
    ) {
        self.client
            .publish_diagnostics(uri, diagnostics, version)
            .await;
    }
}

pub struct Backend {
    diagnostics: DiagnosticService<TowerDiagnosticPublisher>,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            diagnostics: DiagnosticService::new(TowerDiagnosticPublisher { client }),
        }
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(
        &self,
        _: lsp::InitializeParams,
    ) -> tower_lsp::jsonrpc::Result<lsp::InitializeResult> {
        Ok(lsp::InitializeResult {
            capabilities: lsp::ServerCapabilities {
                text_document_sync: Some(lsp::TextDocumentSyncCapability::Kind(
                    lsp::TextDocumentSyncKind::FULL,
                )),
                completion_provider: Some(lsp::CompletionOptions {
                    trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
                    ..Default::default()
                }),
                definition_provider: Some(lsp::OneOf::Left(true)),
                hover_provider: Some(lsp::HoverProviderCapability::Simple(true)),
                semantic_tokens_provider: Some(
                    lsp::SemanticTokensServerCapabilities::SemanticTokensOptions(
                        lsp::SemanticTokensOptions {
                            work_done_progress_options: Default::default(),
                            legend: semantic_tokens_legend(),
                            range: Some(false),
                            full: Some(lsp::SemanticTokensFullOptions::Bool(true)),
                        },
                    ),
                ),
                ..Default::default()
            },
            server_info: Some(lsp::ServerInfo {
                name: "ligare-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: lsp::InitializedParams) {}

    async fn shutdown(&self) -> tower_lsp::jsonrpc::Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: lsp::DidOpenTextDocumentParams) {
        self.diagnostics
            .did_open(
                params.text_document.uri,
                Some(params.text_document.version),
                params.text_document.text,
            )
            .await;
    }

    async fn did_change(&self, params: lsp::DidChangeTextDocumentParams) {
        self.diagnostics
            .did_change(
                params.text_document.uri,
                Some(params.text_document.version),
                params.content_changes,
            )
            .await;
    }

    async fn did_close(&self, params: lsp::DidCloseTextDocumentParams) {
        self.diagnostics.did_close(params.text_document.uri).await;
    }

    async fn completion(
        &self,
        params: lsp::CompletionParams,
    ) -> tower_lsp::jsonrpc::Result<Option<lsp::CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let items = self.diagnostics.completion(&uri, position).await;
        Ok(Some(lsp::CompletionResponse::Array(items)))
    }

    async fn goto_definition(
        &self,
        params: lsp::GotoDefinitionParams,
    ) -> tower_lsp::jsonrpc::Result<Option<lsp::GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        Ok(self.diagnostics.goto_definition(&uri, position).await)
    }

    async fn hover(
        &self,
        params: lsp::HoverParams,
    ) -> tower_lsp::jsonrpc::Result<Option<lsp::Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        Ok(self.diagnostics.hover(&uri, position).await)
    }

    async fn semantic_tokens_full(
        &self,
        params: lsp::SemanticTokensParams,
    ) -> tower_lsp::jsonrpc::Result<Option<lsp::SemanticTokensResult>> {
        let uri = params.text_document.uri;
        Ok(self.diagnostics.semantic_tokens(&uri).await)
    }
}
