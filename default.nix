{ pkgs ? import <nixpkgs> {} }:

let
  s = pkgs.pkgsStatic;
in s.stdenv.mkDerivation {
  pname = "pregnant_frog";
  version = "0.1";

  # Include only the source, not the rootfs tar.
  dontUnpack = true;
  sourceFile = ./pregnant_frog.cpp;

  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ s.libarchive ];

  buildPhase = ''
    runHook preBuild

    $CXX -std=c++17 -O2 -Wall -Wextra -Wpedantic -static \
      $(pkg-config --cflags libarchive) "$sourceFile" \
      -o pregnant_frog $(pkg-config --static --libs libarchive)

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -Dm755 pregnant_frog "$out/bin/pregnant_frog"
    runHook postInstall
  '';

  # Reject an executable that requires a dynamic loader or shared libraries.
  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck

    ${pkgs.binutils}/bin/readelf \
      -lW "$out/bin/pregnant_frog" > program-headers

    ${pkgs.binutils}/bin/readelf \
      -dW "$out/bin/pregnant_frog" > dynamic-entries

    if grep -q INTERP program-headers || grep -q NEEDED dynamic-entries; then
      echo "ERROR: pregnant_frog is not fully statically linked" >&2
      exit 1
    fi

    runHook postInstallCheck
  '';
}
