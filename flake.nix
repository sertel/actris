{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils, ... }: let

    actris = { lib, mkCoqDerivation, coq, iris }: mkCoqDerivation rec {
      pname = "actris";
      propagatedBuildInputs = [ iris ];
      defaultVersion = "0.0.1";
      release."0.0.1" = {
        src = lib.const (lib.cleanSourceWith {
          src = lib.cleanSource ./.;
          filter = let inherit (lib) hasSuffix; in path: type:
            (! hasSuffix ".gitignore" path)
            && (! hasSuffix "flake.nix" path)
            && (! hasSuffix "flake.lock" path)
            && (! hasSuffix "_build" path);
        });
      };
    };

  in flake-utils.lib.eachDefaultSystem (system: let
    pkgs = import nixpkgs {
      inherit system;
      overlays = [ self.overlays.default ];
    };
  in {
    devShells = {
      actris = self.packages.${system}.actris;
      default = self.packages.${system}.actris;
    };

    packages = {
      actris = pkgs.coqPackages_8_19.actris;
      default = self.packages.${system}.actris;
    };
  }) // {
    # NOTE: To use this flake, apply the following overlay to nixpkgs and use
    # the injected package from its respective coqPackages_VER attribute set!
    overlays.default = final: prev: let
      injectPkg = name: set:
        prev.${name}.overrideScope (self: _: {
          actris = self.callPackage actris {};
        });
    in (nixpkgs.lib.mapAttrs injectPkg {
      inherit (final) coqPackages_8_19;
    });
  };
}