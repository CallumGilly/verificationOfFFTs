{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "verificationOfFFTs-env";

  buildInputs = [
    pkgs.python311
    pkgs.python311Packages.pip
    pkgs.python311Packages.numpy

    pkgs.llvmPackages_21.libcxxClang
    pkgs.clang-tools
    pkgs.libgcc

    pkgs.gnumake
  ];
}

