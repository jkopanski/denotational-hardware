args@{ agdaPackages ? "agdaPackages"

, rev    ? "61d24cba72831201efcab419f19b947cf63a2d61"
, sha256 ? "10yi7pp764vz0ikplqysdbyw104gwh967yxis5zizcz0jksc27jn"

, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/jwiegley/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
    overlays = [];
  }
}:

with pkgs.${agdaPackages};

pkgs.stdenv.mkDerivation rec {
  name = "denotational-hardware-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [
    (agda.withPackages (p: [p.standard-library]))
    pkgs.graphviz
    pkgs.git
    pkgs.haskellPackages.pandoc
  ];

  libraryFile = "${libraryName}.agda-lib";
  libraryName = "hardware";

  phases = [ "unpackPhase" "patchPhase" "buildPhase" "installPhase" ];

  buildPhase = ''
    agda -i "." Everything.agda
  '';

  installPhase = ''
    mkdir -p $out
    cp -pR * $out
  '';

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
