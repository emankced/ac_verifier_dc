(lang dune 3.17)

(name appendix_c_verifier)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name appendix_c_verifier)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml (ppx_inline_test :with-test) menhir)
 (tags
  ("add topics" "to describe" your project)))

(using menhir 3.0)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
