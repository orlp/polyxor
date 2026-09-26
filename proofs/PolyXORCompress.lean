import Mathlib

/-!
# The compression function `compress_axu128`

Defines `compress_axu128` as in `src/reference.rs`. The statement about it is
in `PolyXORCheck.lean`.

The model:

* A 64-bit word is a polynomial over `𝔽₂` of degree `< 64`, bit `i` being the
  coefficient of `Xⁱ`. XOR is addition.
* `clmul` is carryless multiplication: the polynomial product, of degree
  `< 128`, not reduced modulo anything.
* A 128-bit value is an element of an `𝔽₄`-vector space `V`, via an additive
  map `ι` from polynomials, where `𝔽₄ = {0, 1, w, w²}` acts as `gf4mul_w`.
-/

namespace PolyXOR

open Polynomial

/-- A 64-bit word: a polynomial over `𝔽₂` of degree `< 64`. -/
abbrev Word : Type := degreeLT (ZMod 2) 64

/-- Carryless multiplication of two words. -/
noncomputable def clmul (x y : Word) : (ZMod 2)[X] := (x : (ZMod 2)[X]) * y

/-- `𝔽₄ = 𝔽₂[X] / (X² + X + 1)`. -/
abbrev F4 : Type := AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])

/-- The generator `w` of `𝔽₄`, with `w² = w + 1`. -/
noncomputable def w : F4 := AdjoinRoot.root _

/-- `compress_axu128` from `src/reference.rs`, whose outputs are
```
h₀ = (1 1 1 1  0) (ha hb hc hd he)ᵀ
h₁ = (0 1 w w² 1) (ha hb hc hd he)ᵀ
``` -/
noncomputable def compress_axu128 {V : Type} [AddCommGroup V] [Module F4 V]
    (ι : (ZMod 2)[X] →+ V) (a b c d : Word × Word) : V × V :=
  let e : Word × Word := (a.1 + b.1 + c.1 + d.1, a.2 + b.2 + c.2 + d.2)
  let ha := clmul a.1 a.2
  let hb := clmul b.1 b.2
  let hc := clmul c.1 c.2
  let hd := clmul d.1 d.2
  let he := clmul e.1 e.2
  (ι (ha + hb + hc + hd), ι hb + w • ι hc + w ^ 2 • ι hd + ι he)

/-- An input: the four arguments `a, b, c, d` of `compress_axu128`. -/
abbrev Block : Type := Fin 4 → Word × Word

/-- `compress_axu128` applied to a `Block`. -/
noncomputable def compress {V : Type} [AddCommGroup V] [Module F4 V]
    (ι : (ZMod 2)[X] →+ V) (x : Block) : V × V :=
  compress_axu128 ι (x 0) (x 1) (x 2) (x 3)

end PolyXOR
