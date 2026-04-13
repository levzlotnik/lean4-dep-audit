{
  description = "lean4-dep-audit: Audit Lean 4 expressions for dependencies (axioms, opaques, constants)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.elan       # Lean 4 version manager
            pkgs.git        # Essential for flakes and lake
          ];

          shellHook = ''
            echo "Welcome to lean4-dep-audit development environment!"
            echo "Run 'lake build' to compile the Lean code."
          '';
        };
      }
    );
}
