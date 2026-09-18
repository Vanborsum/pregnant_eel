{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  nativeBuildInputs = [
    pkgs.gcc
  ];

  buildInputs = [
    pkgs.glibc.static
  ];
}
