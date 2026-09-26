# Lean proofs

This directory contains Lean proofs that the compression function
`compress_axu128` is 2^-128 almost-XOR-universal, and that the full hash
PolyXOR128 is `(L/4096 + 3) / 2^128` almost-XOR-universal on messages of at most
L bytes.

To check the results you need to read three files:

- [`PolyXORCompress.lean`](PolyXORCompress.lean) models `compress_axu128`
  from `src/reference.rs`.
- [`PolyXORFull.lean`](PolyXORFull.lean) models the full hash (`update` + `finalize_raw`).
- [`PolyXORCheck.lean`](PolyXORCheck.lean) states the two theorems.

The proofs are in [`PolyXOR/CompressProof/`](PolyXOR/CompressProof) and
[`PolyXOR/FullProof/`](PolyXOR/FullProof). To check them, run

```
lake build
```

A successful build prints the axioms each theorem depends on, which should be
only Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

All Lean files are fully AI-generated, but the hash modeling and theorem files
have been manually checked that they match the implemented hash function.
