import PolyXORCompress

/-!
# The full hash PolyXOR128

Defines `finalize_raw` of PolyXOR128 as in `src/lib.rs` and `src/reference.rs`,
reusing `compress_axu128` from `PolyXORCompress.lean`. The statement about it is
in `PolyXORCheck.lean`.
-/

namespace PolyXOR

open Polynomial

/-- A byte, as its eight bits. -/
abbrev Byte : Type := Fin 8 → ZMod 2

/-- Byte `n` of `m`, zero past the end. -/
def byteAt (m : List Byte) (n : ℕ) : Byte := m.getD n 0

/-- Word `n` of `m`, loaded little-endian, zero past the end. -/
noncomputable def wordAt (m : List Byte) (n : ℕ) : Word :=
  (degreeLTEquiv (ZMod 2) 64).symm fun k =>
    byteAt m (8 * n + k / 8) ⟨k % 8, Nat.mod_lt _ (by norm_num)⟩

/-- `count as u128`, as a polynomial. -/
noncomputable def lenPoly (n : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 64, if n.testBit i then X ^ i else 0

/-- The number of 128-byte blocks, after zero-padding. -/
def numBlocks (m : List Byte) : ℕ := (m.length + 127) / 128

/-- The number of 4096-byte chunks. -/
def numChunks (m : List Byte) : ℕ := (numBlocks m + 31) / 32

/-- A key: the block key, `z`, `u` and `y`. -/
abbrev Key (F : Type) : Type := (Fin 32 → Fin 16 → Word) × F × F × F

variable {F : Type} [Field F] [Module F4 F]

/-- `hash_block` from `src/reference.rs`, on the XOR of the data and key words. -/
noncomputable def hashBlock (ι : (ZMod 2)[X] →+ F) (m : Fin 16 → Word) : F × F :=
  compress_axu128 ι (m 0, m 12) (m 2, m 14) (m 8, m 4) (m 10, m 6) +
    compress_axu128 ι (m 1, m 13) (m 3, m 15) (m 9, m 5) (m 11, m 7)

/-- The digest `(h₀, h₁)` of chunk `c`. -/
noncomputable def chunkDigest (ι : (ZMod 2)[X] →+ F) (block : Fin 32 → Fin 16 → Word)
    (m : List Byte) (c : ℕ) : F × F :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin 32 => 32 * c + b < numBlocks m),
    hashBlock ι fun i => wordAt m (16 * (32 * c + b) + i) + block b i

/-- `finalize_raw` of `m`. -/
noncomputable def polyxor128 (ι : (ZMod 2)[X] →+ F) (k : Key F) (m : List Byte) : F :=
  let (block, z, u, y) := k
  let acc := (List.range (numChunks m)).foldl
    (fun acc c => (acc + u) * ((chunkDigest ι block m c).2 + y) + (chunkDigest ι block m c).1) z
  (acc + u) * (ι (lenPoly m.length) + y)

end PolyXOR
