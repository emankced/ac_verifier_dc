let
  pkgs = import <nixpkgs> {};
in pkgs.mkShell rec {
  #nativeInputs = with pkgs; [
  #  ocaml
  #  #opam
  #];

  buildInputs = with pkgs; [
    ocaml
    dune_3
    ocamlPackages.findlib
    ocamlPackages.ocaml-lsp
    ocamlPackages.odoc
    ocamlformat
    ocamlPackages.utop

    ocamlPackages.z3
    ocamlPackages.menhir
    ocamlPackages.ppx_inline_test
  ];
}
