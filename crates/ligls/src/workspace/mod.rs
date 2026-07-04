pub(crate) mod project;

pub(crate) use project::{
    ModuleKey, ProjectContext, fallback_file_candidates, fallback_imported_module_keys,
    fallback_module_key, project_context_for_uri, workspace_root_for_uris,
};
