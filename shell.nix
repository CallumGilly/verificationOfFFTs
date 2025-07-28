{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "verificationOfFFTs-env";

  buildInputs = [
    pkgs.python311
    pkgs.python311Packages.pip
    pkgs.python311Packages.numpy
  ];
}

