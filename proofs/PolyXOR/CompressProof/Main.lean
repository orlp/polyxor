import PolyXORCompress
import PolyXOR.CompressProof.Core

/-!
# Proof of `compress_axu128_is_axu`

`PolyXOR.CompressProof.Core` proves the bound for an abstract version of the compression
function, indexed by `Idx = Fin 4 × Fin 2` and phrased in terms of the output
difference `D`. This file specializes it to `𝔽₄` and translates it to the
statement in `PolyXORCheck.lean`.
-/

namespace PolyXOR.CompressProof

open Polynomial

/-! ### `𝔽₄` -/

lemma degree_f4 : (X ^ 2 + X + 1 : R).degree = 2 := by
  compute_degree!

instance : Nontrivial F4 := AdjoinRoot.nontrivial _ (by rw [degree_f4]; decide)

lemma algebraMap_F4_injective : Function.Injective (algebraMap (ZMod 2) F4) :=
  AdjoinRoot.coe_injective (by rw [degree_f4]; decide)

instance : CharP F4 2 := charP_of_injective_algebraMap algebraMap_F4_injective 2

lemma w_sq : w ^ 2 = w + 1 := by
  have h : aeval (AdjoinRoot.root (X ^ 2 + X + 1 : R)) (X ^ 2 + X + 1 : R) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [map_add, map_pow, aeval_X, map_one] at h
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  simp only [w]
  linear_combination h - (AdjoinRoot.root (X ^ 2 + X + 1 : R) + 1) * h2

/-! ### Blocks as functions on `Idx` -/

/-- The two words of an argument, indexed by `Fin 2`. -/
def half (p : Word × Word) : Fin 2 → Word
  | 0 => p.1
  | 1 => p.2

@[simp] lemma half_zero (p : Word × Word) : half p 0 = p.1 := rfl
@[simp] lemma half_one (p : Word × Word) : half p 1 = p.2 := rfl

/-- A `Block` as a function on `Idx`, the indexing used in `PolyXOR.CompressProof.Core`. -/
def flat : Block ≃+ (Idx → Wd) where
  toFun x z := half (x z.1) z.2
  invFun K i := (K (i, 0), K (i, 1))
  left_inv _ := rfl
  right_inv K := by funext ⟨i, l⟩; fin_cases l <;> rfl
  map_add' x y := by funext ⟨i, l⟩; fin_cases l <;> rfl

@[simp] lemma flat_apply (x : Block) (i : Fin 4) (l : Fin 2) : flat x (i, l) = half (x i) l :=
  rfl

variable {V : Type} [AddCommGroup V] [Module F4 V]

/-- `H` from `PolyXOR.CompressProof.Core` is `compress`. -/
lemma H_flat (ι : R →+ V) (x : Block) : H w ι (fun z => (flat x z : R)) = compress ι x := by
  simp only [H, compress, compress_axu128, clmul, clnh, esum, beta, Fin.sum_univ_four,
    flat_apply, half_zero, half_one, Submodule.coe_add, zero_smul, one_smul, zero_add]
  refine Prod.ext ?_ ?_ <;> simp only [map_add, add_assoc]

/-! ### The theorem -/

theorem compress_axu128_is_axu (V : Type) [AddCommGroup V] [Module F4 V]
    (ι : (ZMod 2)[X] →+ V) (hι : ∀ x : (ZMod 2)[X], x.degree < 128 → ι x = 0 → x = 0)
    (m m' : Block) (hm : m ≠ m') (γ : V × V) :
    (Nat.card {k : Block // compress ι (m + k) + compress ι (m' + k) = γ} : ℚ)
      / Nat.card Block ≤ 1 / 2 ^ 128 := by
  set δ : Idx → Wd := flat (m - m')
  have hδ : δ ≠ 0 := fun h => hm (sub_eq_zero.mp (flat.injective (h.trans (map_zero flat).symm)))
  have hbound := card_diff_le w w_sq ι hι δ hδ γ
  -- `k ↦ flat (m' + k)` identifies the keys realizing `γ` with those counted in `Core`.
  have hcard : Nat.card {k : Block // compress ι (m + k) + compress ι (m' + k) = γ}
      = Nat.card {K : Idx → Wd // D w ι (fun z => (δ z : R)) (fun z => (K z : R)) = γ} := by
    refine Nat.card_congr (((Equiv.addLeft m').trans flat.toEquiv).subtypeEquiv fun k => ?_)
    have hK : (fun z => (flat (m' + k) z : R)) + (fun z => (δ z : R))
        = fun z => (flat (m + k) z : R) := by
      funext z
      rw [Pi.add_apply, ← Submodule.coe_add, ← Pi.add_apply (flat (m' + k)), ← map_add]
      congr 3
      abel_nf
    simp only [Equiv.trans_apply, Equiv.coe_addLeft, AddEquiv.toEquiv_eq_coe,
      AddEquiv.coe_toEquiv]
    rw [D, hK, H_flat, H_flat, sub_eq_add_neg, neg_self F4]
  have hcardB : Nat.card Block = Nat.card (Idx → Wd) := Nat.card_congr flat.toEquiv
  have hpos : (0 : ℚ) < Nat.card (Idx → Wd) := by exact_mod_cast Nat.card_pos
  rw [hcard, hcardB, div_le_div_iff₀ hpos (by positivity), one_mul]
  exact_mod_cast hbound

/-- The hypothesis on `ι` is satisfiable: view an `𝔽₂`-polynomial as an
`𝔽₄`-polynomial. -/
example : ∃ ι : R →+ F4[X], ∀ x : R, x.degree < 128 → ι x = 0 → x = 0 :=
  ⟨(mapRingHom (algebraMap (ZMod 2) F4)).toAddMonoidHom, fun _ _ hx =>
    map_injective _ algebraMap_F4_injective (by simpa using hx)⟩

end PolyXOR.CompressProof
