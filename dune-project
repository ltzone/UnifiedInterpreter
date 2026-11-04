(lang dune 3.11)

(name unified_interpreter)

(generate_opam_files true)

(package
 (name unified_interpreter)
 (synopsis "A small OCaml 5 effect-based multi-level IR interpreter demo")
 (depends
  (ocaml (>= 5.0))
  dune
  rocq-prover
  (rocq-stdpp (= 1.13.0))
  (coq-ext-lib (= 0.13.1))
  (coq-itree (= 5.2.1))
  (rocq-coinduction (= 1.21))
  zarith
  yojson))
