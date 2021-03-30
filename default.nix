# The build system where packages will be built.
{ system ? builtins.currentSystem
  # The host system where packages will run.
, crossSystem ? null
  # Additional sources.json overrides.
, sources ? { }
  # Additional nixpkgs.config overrides.
, config ? { }
  # Additional nixpkgs.overlays.
, overlays ? [ ]
  # Overlays to apply to the last package set in cross compilation.
, crossOverlays ? [ ]
  # The GHC version to use. (compiler-nix-name in haskell.nix)
, ghcVersion ? "ghc8104" }:

let

  pkgs = import ./nix/default.nix {
    inherit system sources config overlays crossOverlays ghcVersion;
  };

  projectPackages =
    pkgs.haskell-nix.haskellLib.selectProjectPackages pkgs.cabalProject;

  collectChecks = _:
    pkgs.recurseIntoAttrs (builtins.mapAttrs (_: p: p.checks) projectPackages);
  collectComponents = type:
    pkgs.haskell-nix.haskellLib.collectComponents' type projectPackages;

in projectPackages // {
  ci = builtins.mapAttrs (type: f: f type) {
    "library" = collectComponents;
    "tests" = collectComponents;
    "benchmarks" = collectComponents;
    "exes" = collectComponents;
    "checks" = collectChecks;
  };

  shell = pkgs.cabalProject.shellFor {
    exactDeps = true;
    withHoogle = false;

    packages = ps:
      with ps; [
        amazonka
        amazonka-core
        amazonka-test
        amazonka-gen
      ];

    tools = {
      cabal = "3.2.0.0";
      cabal-fmt = "0.1.5.1";
      shellcheck = "0.7.1";
    };

    buildInputs = [
      pkgs.nixfmt
      pkgs.shfmt

      (import pkgs.sources.niv { }).niv
    ];
  };
}
