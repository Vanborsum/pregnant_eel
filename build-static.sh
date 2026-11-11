#!/usr/bin/env bash
# Build the scanner beside this script. Nix supplies musl and static libarchive.
# On a system with a native static development toolchain, use --native.
set -euo pipefail

compile() {
    local source=$1 output=$2
    local -a cflags libs
    read -r -a cflags <<< "$(pkg-config --cflags libarchive)"
    read -r -a libs <<< "$(pkg-config --static --libs libarchive)"
    "${CXX:-c++}" -std=c++17 -O2 -Wall -Wextra -Wpedantic -static \
        "${cflags[@]}" "$source" -o "$output" "${libs[@]}"

    local headers
    headers=$(readelf -lW -dW "$output")
    if grep -Eq '(^[[:space:]]*INTERP[[:space:]]|\(NEEDED\))' <<< "$headers"; then
        echo "The executable requires a dynamic loader or shared libraries." >&2
        return 1
    fi
}

# The Nix builder passes store paths, since it builds outside the source tree.
if [[ ${1:-} == --compile ]]; then
    mkdir -p "$(dirname -- "$3")"
    compile "$2" "$3"
    exit
fi

cd -- "$(dirname -- "$0")"
if [[ ${1:-} == --native ]] || ! command -v nix-build >/dev/null; then
    build_dir=$(mktemp -d .raccoon-build-XXXXXX)
    trap 'rm -rf -- "$build_dir"' EXIT
    compile pregnant_raccoon.cpp "$build_dir/pregnant_raccoon"
    mv -f -- "$build_dir/pregnant_raccoon" pregnant_raccoon
else
    result=$(nix-build --no-out-link --expr '
        let pkgs = import <nixpkgs> {}; s = pkgs.pkgsStatic;
        in s.stdenv.mkDerivation {
            name = "pregnant-raccoon-static";
            sourceFile = ./pregnant_raccoon.cpp;
            script = ./build-static.sh;
            nativeBuildInputs = [ pkgs.pkg-config pkgs.binutils ];
            buildInputs = [ s.libarchive ];
            buildCommand = "bash $script --compile $sourceFile $out/bin/pregnant_raccoon";
        }')
    install -m755 "$result/bin/pregnant_raccoon" ./pregnant_raccoon
fi
echo "Built ./pregnant_raccoon"
