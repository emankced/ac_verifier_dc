let
  pkgs = import <nixpkgs> {};
in pkgs.mkShell rec {
  buildInputs = with pkgs; [
    ocaml
    dune_3
    z3
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
