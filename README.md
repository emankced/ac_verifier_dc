# Appendix C Verifier
This is not the final name.

## Building and Running
Dependencies can be installed by running:
```
# if you want a local opam switch run:
#opam switch create .
opam install . --deps-only --with-test --with-doc
```

The project can be built by running:
```
opam exec -- dune build
```

The program can be started by running:
```
opam exec -- dune exec appendix_c_verifier
```

The tests can be executed by running:
```
opam exec -- dune test
```
