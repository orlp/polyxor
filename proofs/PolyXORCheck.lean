import PolyXOR.CompressProof.Main
import PolyXOR.FullProof.Main

/-!
# The theorems

The two results, about the definitions in `PolyXORCompress.lean` and
`PolyXORFull.lean`. The proofs are in `PolyXOR/CompressProof/` and
`PolyXOR/FullProof/`; if `lake build` succeeds, Lean has checked them, and the
`#print axioms` lines show they use only Lean's standard axioms (no `sorry`).

In both, `ι` maps a 128-bit value, as a polynomial of degree `< 128`, to its
element of `V` or `F`, and the theorems hold for every such `ι`, so the exact
bit layout does not matter. In the second, `F` is `GF(2¹²⁸)` and the
`F4`-module structure on `F` is `gf4mul_w`.
-/

namespace PolyXOR

open Polynomial

/-- **`compress_axu128` is `2⁻¹²⁸`-almost-XOR-universal.**

For any two distinct inputs `m ≠ m'` and any difference `γ`, a uniformly random
key `k` satisfies `compress (m ⊕ k) ⊕ compress (m' ⊕ k) = γ` with probability at
most `2⁻¹²⁸`. -/
theorem compress_axu128_is_axu (V : Type) [AddCommGroup V] [Module F4 V]
    (ι : (ZMod 2)[X] →+ V) (hι : ∀ x : (ZMod 2)[X], x.degree < 128 → ι x = 0 → x = 0)
    (m m' : Block) (hm : m ≠ m') (γ : V × V) :
    (Nat.card {k : Block // compress ι (m + k) + compress ι (m' + k) = γ} : ℚ)
      / Nat.card Block ≤ 1 / 2 ^ 128 :=
  CompressProof.compress_axu128_is_axu V ι hι m m' hm γ

/-- **PolyXOR128 is `(L/4096 + 3) / 2¹²⁸`-almost-XOR-universal.**

For any two distinct messages of at most `L` bytes and any difference `γ`, a
uniformly random key `k` satisfies `polyxor128 k m ⊕ polyxor128 k m' = γ` with
probability at most `(L/4096 + 3) / 2¹²⁸`. -/
theorem polyxor128_axu (F : Type) [Field F] [Fintype F] [Module F4 F]
    (hF : Fintype.card F = 2 ^ 128) (ι : (ZMod 2)[X] →+ F)
    (hι : ∀ x : (ZMod 2)[X], x.degree < 128 → ι x = 0 → x = 0)
    (L : ℕ) (m m' : List Byte) (hm : m ≠ m')
    (hL : m.length ≤ L) (hL' : m'.length ≤ L) (h64 : L < 2 ^ 64) (γ : F) :
    (Nat.card {k : Key F // polyxor128 ι k m + polyxor128 ι k m' = γ} : ℚ)
      / Nat.card (Key F) ≤ ((L : ℚ) / 4096 + 3) / 2 ^ 128 :=
  FullProof.polyxor128_axu F hF ι hι L m m' hm hL hL' h64 γ

#print axioms compress_axu128_is_axu
#print axioms polyxor128_axu

end PolyXOR
