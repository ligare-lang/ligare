{
  description = "Rust development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs =
    {
      self,
      nixpkgs,
      rust-overlay,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
      in
      {
        devShells.default = pkgs.mkShell rec {
          nativeBuildInputs = [ pkgs.pkg-config ];
          buildInputs = with pkgs; [
            clang
            libffi
            libxml2
            zig
            (rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
          ];

          CXXFLAGS_x86_64_unknown_linux_gnu = "-O2";

          # https://github.com/rust-lang/rust-bindgen#environment-variables
          LIBCLANG_PATH = pkgs.lib.makeLibraryPath [ pkgs.llvmPackages.libclang.lib ];

          shellHook = ''
            export PATH=$PATH:''${CARGO_HOME:-~/.cargo}/bin
          '';

          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath (buildInputs ++ nativeBuildInputs);

          # Add glibc, clang, glib, and other headers to bindgen search path
          BINDGEN_EXTRA_CLANG_ARGS =
            # Includes normal include path
            (builtins.map (a: ''-I"${a}/include"'') [
              # add dev libraries here (e.g. pkgs.libvmi.dev)
              pkgs.glibc.dev
            ])
            # Includes with special directory paths
            ++ [
              ''-I"${pkgs.llvmPackages.libclang.lib}/lib/clang/${pkgs.llvmPackages.libclang.version}/include"''
              ''-I"${pkgs.glib.dev}/include/glib-2.0"''
              ''-I${pkgs.glib.out}/lib/glib-2.0/include/''
            ];
        };
      }
    );
}
