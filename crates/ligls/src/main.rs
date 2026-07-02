use tower_lsp::{LspService, Server};

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(ligls::Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}
