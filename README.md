# Hylomorphisms in Rocq

## Requirements

- Rocq Prover >= 9.2 (tested with 9.3.0)
- Rocq Stdlib
- Paco >= 4.2.3 (opam package `coq-paco`)
- Dune >= 3.21

## Building

```
opam install . --deps-only
dune build
```

`dune install` installs the `Hylo` library and `Hylo.Examples`. Use the library
with `From Hylo Require Import Hylo.`; the helper lemmas in `Hylo.Utils`
(including the `is_true` coercion) are not re-exported, so import them where needed.
The OCaml code extracted from the examples (`extraction/*/Extr*.v`) is written to
`_build/default/extraction/<example>/`; the shared extraction settings
(`extraction-setup/`, `Hylo.Extraction`) are not installed.
`rocq-hylomorphisms.opam` is generated from `dune-project`; edit that instead.

`_RocqProject` is only for editors (Proof General, VsRocq, rocq-lsp): it
points them at the compiled files in `_build`, so run `dune build` first.

## License

GPL-3.0; see `LICENSE.txt`.
