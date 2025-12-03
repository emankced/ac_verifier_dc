(lang dune 3.17)

(name dc)

(generate_opam_files true)

;(source
; (github username/reponame))

(authors "Jonas Pflanzer <noreply@example.com>")

;(maintainers "Maintainer Name <maintainer@example.com>")

;(license LICENSE)

;(documentation https://url/to/documentation)

(package
 (name dc)
 (synopsis "DC, the program verifier for AC.")
 (description "DC is a program verifier for the AC programming language, that is designed to keep it simple. The verification is based on symbolic execution, while the assertion language supports separation logic.")
 (depends ocaml (ppx_inline_test :with-test) menhir z3)
 (tags
  ("DC" "AC" "verifier" "formal verification" "symbolic execution" "separation logic")))

(using menhir 3.0)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
