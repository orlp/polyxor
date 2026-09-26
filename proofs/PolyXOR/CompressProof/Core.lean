import PolyXOR.CompressProof.Descent

set_option linter.unusedSectionVars false

/-!
# The main counting argument

This file proves `card_diff_le`, the core of `compress_axu128_is_axu`, for an
abstract version of the compression function `H`. The inputs are indexed by
`Idx = Fin 4 × Fin 2`: word `(i, l)` is word `l` of argument `i`. The ring of
scalars is any commutative ring `A` of characteristic two with an element `w`
satisfying `w² = w + 1`, and `M` is any `A`-module.

## Outline

Fix a nonzero input difference `δ` and write `D K = H (K + δ) - H K` for the
output difference at key `K`.

1. `D` is affine in `K` (`D_sub`), with linear part `L`. This is because
   `(x₀ + δ₀)(x₁ + δ₁) - x₀ x₁ = δ₀ x₁ + δ₁ x₀ + δ₀ δ₁`.

2. Suppose there are two words `P ≠ Q` such that `L` is injective on keys
   supported on `{P, Q}` (`exists_pivot`). Then two keys that agree outside
   `{P, Q}` and have the same `D` are equal, so each of the `(2⁶⁴)⁶` choices for
   the other six words contributes at most one key (`card_pivot_le`). That gives
   at most `2³⁸⁴ = 2⁵¹² / 2¹²⁸` keys.

3. `exists_pivot` finds `P` and `Q`. Write `e = δ₀ + δ₁ + δ₂ + δ₃` for the
   difference of the fifth argument. The word `(i, 1 - σ)` has coefficient
   `δᵢ,σ` in the first output and `βᵢ δᵢ,σ + eσ` in the second, where
   `(β₀, β₁, β₂, β₃) = (0, 1, w, w²)` (`L_sparse`).

   * Case A, `e = 0`. At least two arguments have a nonzero difference, since
     one alone would make `e ≠ 0`. Take a nonzero word in each; the injectivity
     follows because `βᵢ - βⱼ` is a unit (`two_word_caseA`).

   * Case B, `eσ ≠ 0`. Take both words in half `1 - σ` of arguments `{0, 1}` or
     of arguments `{2, 3}`, the two pairs with `βᵢ + βⱼ = 1`. The linear part is
     injective if the determinant `s eσ + t eσ + s t` is nonzero, where `s`, `t`
     are the differences of the other halves (`two_word_caseB`).
     `no_excluded_system` in `PolyXOR.CompressProof.Descent` shows it cannot vanish for both
     pairs.
-/

namespace PolyXOR.CompressProof

open Polynomial

/-! ### Degrees -/

lemma degree_mul_lt_128 {p q : R} (hp : p.degree < 64) (hq : q.degree < 64) :
    (p * q).degree < 128 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
  rcases eq_or_ne q 0 with rfl | hq0
  · simp only [mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
  rw [Polynomial.degree_eq_natDegree hp0] at hp
  rw [Polynomial.degree_eq_natDegree hq0] at hq
  rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hp0,
    Polynomial.degree_eq_natDegree hq0]
  norm_cast at hp hq ⊢
  omega

lemma degree_add_lt_128 {p q : R} (hp : p.degree < 128) (hq : q.degree < 128) :
    (p + q).degree < 128 :=
  lt_of_le_of_lt (Polynomial.degree_add_le p q) (max_lt hp hq)

/-! ### The scalars

`A` is any commutative ring of characteristic two with an element `w` satisfying
`w² = w + 1`. -/

section Scalars

variable {A : Type*} [CommRing A] [CharP A 2] {w : A}

/-- `w` is a cube root of unity, so `w` and `w² = w + 1` are units. -/
lemma w_cube (hw : w ^ 2 = w + 1) : w * w ^ 2 = 1 := by
  have h2 : (2 : A) = 0 := CharTwo.two_eq_zero
  linear_combination (w + 1) * hw + w * h2

/-- The four `𝔽₄`-coefficients of the second output row: the five columns of the
`2 × 5` matrix are the five points of the projective line over `𝔽₄`. -/
def beta (w : A) : Fin 4 → A
  | 0 => 0
  | 1 => 1
  | 2 => w
  | 3 => w ^ 2

lemma isUnit_w (hw : w ^ 2 = w + 1) : IsUnit w :=
  IsUnit.of_mul_eq_one _ (w_cube hw)

lemma isUnit_w_sq (hw : w ^ 2 = w + 1) : IsUnit (w ^ 2) :=
  IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact w_cube hw)

/-- Any two of the four coefficients differ by a unit: they are four distinct
points of `𝔽₄`, and every nonzero element of `𝔽₄` is a unit. -/
lemma isUnit_beta_sub (hw : w ^ 2 = w + 1) {i j : Fin 4} (hij : i ≠ j) :
    IsUnit (beta w i - beta w j) := by
  have h2 : (2 : A) = 0 := CharTwo.two_eq_zero
  have key : beta w i - beta w j = 1 ∨ beta w i - beta w j = w ∨
      beta w i - beta w j = w ^ 2 := by
    fin_cases i <;> fin_cases j <;> simp only [beta] <;>
      first
        | exact absurd rfl hij
        | (left; linear_combination (0 : A) * h2)
        | (right; left; linear_combination (0 : A) * h2)
        | (right; right; linear_combination (0 : A) * h2)
        | (left; linear_combination -h2)
        | (right; left; linear_combination -w * h2)
        | (right; right; linear_combination -(w ^ 2) * h2)
        | (right; right; linear_combination -hw - w * h2)
        | (right; left; linear_combination -hw - w * h2)
        | (right; right; linear_combination -hw - h2)
        | (left; linear_combination -hw - h2)
        | (right; left; linear_combination hw)
        | (left; linear_combination hw)
  rcases key with h | h | h
  · rw [h]; exact isUnit_one
  · rw [h]; exact isUnit_w hw
  · rw [h]; exact isUnit_w_sq hw

/-- `{a, b}` and `{c, d}` are the two disjoint pairs whose coefficients sum
to `1`; Case B of the rank argument runs on one of them. -/
lemma beta_pair01 : beta w 0 + beta w 1 = 1 := by simp [beta]

lemma beta_pair23 (hw : w ^ 2 = w + 1) : beta w 2 + beta w 3 = 1 := by
  have h2 : (2 : A) = 0 := CharTwo.two_eq_zero
  simp only [beta]
  linear_combination hw + w * h2

end Scalars

/-! ### Injectivity on two words

`u` and `v` are the key differences in two words of different arguments, `s`
and `t` their coefficients in the first output, and `ε` the coefficient
contributed through `e`. -/

section TwoWord

variable {M : Type*} [AddCommGroup M]

lemma neg_self (A : Type*) [CommRing A] [CharP A 2] [Module A M] (x : M) : -x = x := by
  have h : ((-1 : A)) • x = ((1 : A)) • x := by rw [CharTwo.neg_eq]
  simpa using h

variable {A : Type*} [CommRing A] [CharP A 2] [Module A M]

/-- Case A (`e = 0`): the two arguments have distinct `β`s and `e` contributes
nothing. -/
lemma two_word_caseA (ι : R →+ M) (hι : ∀ x : R, x.degree < 128 → ι x = 0 → x = 0)
    {s t u v : R} {bi bj : A}
    (hs : s ≠ 0) (ht : t ≠ 0)
    (hsd : s.degree < 64) (htd : t.degree < 64)
    (hud : u.degree < 64) (hvd : v.degree < 64)
    (hβ : IsUnit (bi - bj))
    (h0 : ι (s * u) + ι (t * v) = 0)
    (h1 : bi • ι (s * u) + bj • ι (t * v) = 0) :
    u = 0 ∧ v = 0 := by
  have hV : ι (t * v) = -ι (s * u) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0
  have hkey : (bi - bj) • ι (s * u) = 0 := by
    rw [sub_smul, sub_eq_add_neg, ← smul_neg, ← hV]; exact h1
  obtain ⟨c, hc⟩ := hβ.exists_left_inv
  have hU : ι (s * u) = 0 := by
    have h2 := congrArg (fun m : M => c • m) hkey
    simpa [smul_smul, hc] using h2
  have hu : u = 0 := by
    have := hι _ (degree_mul_lt_128 hsd hud) hU
    exact (mul_eq_zero.mp this).resolve_left hs
  refine ⟨hu, ?_⟩
  have hV0 : ι (t * v) = 0 := by rw [hV, hU, neg_zero]
  have := hι _ (degree_mul_lt_128 htd hvd) hV0
  exact (mul_eq_zero.mp this).resolve_left ht

/-- Case B (`e ≠ 0`): the two arguments are a pair whose `β`s sum to `1`, and
the determinant `s ε + t ε + s t` is nonzero. -/
lemma two_word_caseB (ι : R →+ M) (hι : ∀ x : R, x.degree < 128 → ι x = 0 → x = 0)
    {s t ε u v : R} {bi bj : A}
    (hsd : s.degree < 64) (htd : t.degree < 64) (hεd : ε.degree < 64)
    (hud : u.degree < 64) (hvd : v.degree < 64)
    (hβ : bi + bj = 1)
    (hdet : s * ε + t * ε + s * t ≠ 0)
    (h0 : ι (s * u) + ι (t * v) = 0)
    (h1 : bi • ι (s * u) + bj • ι (t * v) + (ι (ε * u) + ι (ε * v)) = 0) :
    u = 0 ∧ v = 0 := by
  have e1 : s * u + t * v = 0 := by
    refine hι _ (degree_add_lt_128 (degree_mul_lt_128 hsd hud)
      (degree_mul_lt_128 htd hvd)) ?_
    rw [map_add]; exact h0
  -- in characteristic two the two halves of the first row are equal
  have hV : ι (t * v) = ι (s * u) := by
    have h : ι (t * v) = -ι (s * u) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0
    rw [h, neg_self A]
  rw [hV, ← add_smul, hβ, one_smul] at h1
  have e2 : s * u + ε * u + ε * v = 0 := by
    refine hι _ (degree_add_lt_128 (degree_add_lt_128 (degree_mul_lt_128 hsd hud)
      (degree_mul_lt_128 hεd hud)) (degree_mul_lt_128 hεd hvd)) ?_
    rw [map_add, map_add]
    rw [← add_assoc] at h1
    exact h1
  constructor
  · have hz : (s * ε + t * ε + s * t) * u = 0 := by
      linear_combination₂ ε * e1 + t * e2
    exact (mul_eq_zero.mp hz).resolve_left hdet
  · have hz : (s * ε + t * ε + s * t) * v = 0 := by
      linear_combination₂ (s + ε) * e1 + s * e2
    exact (mul_eq_zero.mp hz).resolve_left hdet

end TwoWord

/-! ### The compression function -/

section Hash

/-- The eight words of an input: word `l` of argument `i`. -/
abbrev Idx := Fin 4 × Fin 2

/-- The other word of the same argument. -/
def sw : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

@[simp] lemma sw_zero : sw 0 = 1 := rfl
@[simp] lemma sw_one : sw 1 = 0 := rfl
@[simp] lemma sw_sw (l : Fin 2) : sw (sw l) = l := by fin_cases l <;> rfl

variable {M : Type*} [AddCommGroup M] {A : Type*} [CommRing A] [CharP A 2] [Module A M]

/-- The unreduced carryless product of the two words of argument `i`. -/
noncomputable def clnh (K : Idx → R) (i : Fin 4) : R := K (i, 0) * K (i, 1)

/-- Word `l` of the fifth argument `e`, the sum of the four arguments. -/
noncomputable def esum (K : Idx → R) (l : Fin 2) : R := ∑ i : Fin 4, K (i, l)

/-- The compression function `H`, with the `2 × 5` combining matrix
`(1 1 1 1 0 ; 0 1 w w² 1)`. -/
noncomputable def H (w : A) (ι : R →+ M) (K : Idx → R) : M × M :=
  (∑ i : Fin 4, ι (clnh K i),
    (∑ i : Fin 4, beta w i • ι (clnh K i)) + ι (esum K 0 * esum K 1))

/-- The differential of `H` at message difference `d`. -/
noncomputable def D (w : A) (ι : R →+ M) (d K : Idx → R) : M × M := H w ι (K + d) - H w ι K

/-- The linear part of `D`, as a function of the key words. -/
noncomputable def L (w : A) (ι : R →+ M) (d y : Idx → R) : M × M :=
  (∑ z : Idx, ι (d (z.1, sw z.2) * y z),
    (∑ z : Idx, beta w z.1 • ι (d (z.1, sw z.2) * y z))
      + ∑ z : Idx, ι (esum d (sw z.2) * y z))

/-- The differential of `clnh`, in two-point form: the key cancels from the
difference of the two executions, leaving an expression linear in `y = K ⊖ K'`. -/
lemma clnh_two_point (ι : R →+ M) (d K K' : Idx → R) (i : Fin 4) :
    (ι (clnh (K + d) i) - ι (clnh K i)) - (ι (clnh (K' + d) i) - ι (clnh K' i))
      = ι (d (i, 1) * (K - K') (i, 0)) + ι (d (i, 0) * (K - K') (i, 1)) := by
  have hc : ∀ a b : R, ι a - ι b = ι (a - b) := fun a b => (map_sub ι a b).symm
  rw [hc, hc, hc, ← map_add]
  congr 1
  simp only [clnh, Pi.add_apply, Pi.sub_apply]
  ring

lemma esum_add (d K : Idx → R) (l : Fin 2) : esum (K + d) l = esum K l + esum d l := by
  simp [esum, Finset.sum_add_distrib]

lemma esum_sub (K K' : Idx → R) (l : Fin 2) : esum (K - K') l = esum K l - esum K' l := by
  simp [esum, Finset.sum_sub_distrib]

/-- Sum over `Idx` of a term that only sees `y z`, unfolded to a sum over
arguments of the two words. -/
lemma sum_idx_halves {N : Type*} [AddCommMonoid N] (f : Idx → N) :
    ∑ z : Idx, f z = ∑ i : Fin 4, (f (i, 0) + f (i, 1)) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => by rw [Fin.sum_univ_two]

/-- `D K ⊖ D K' = L (K ⊖ K')`: the differential is affine, with linear part `L`. -/
lemma D_sub (w : A) (ι : R →+ M) (d K K' : Idx → R) :
    D w ι d K - D w ι d K' = L w ι d (K - K') := by
  have hpt := clnh_two_point ι d K K'
  refine Prod.ext ?_ ?_
  · simp only [D, H, L, Prod.fst_sub]
    rw [sum_idx_halves]
    simp only [sw_zero, sw_one]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hpt i
  · simp only [D, H, L, Prod.snd_sub]
    have hsplit : ∀ a1 a2 a3 a4 b1 b2 b3 b4 : M,
        ((a1 + b1) - (a2 + b2)) - ((a3 + b3) - (a4 + b4))
          = ((a1 - a2) - (a3 - a4)) + ((b1 - b2) - (b3 - b4)) := by intros; abel
    rw [hsplit]
    congr 1
    · rw [sum_idx_halves]
      simp only [sw_zero, sw_one]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← smul_sub, ← smul_sub, ← smul_sub, hpt i, smul_add]
    · rw [sum_idx_halves]
      simp only [sw_zero, sw_one]
      have hc : ∀ a b : R, ι a - ι b = ι (a - b) := fun a b => (map_sub ι a b).symm
      rw [hc, hc, hc]
      have hR : ∑ i : Fin 4, (ι (esum d 1 * (K - K') (i, 0)) + ι (esum d 0 * (K - K') (i, 1)))
          = ι (esum d 1 * esum (K - K') 0 + esum d 0 * esum (K - K') 1) := by
        generalize esum d 1 = E1
        generalize esum d 0 = E0
        simp only [esum, map_add, Finset.mul_sum, map_sum]
        rw [← Finset.sum_add_distrib]
      rw [hR]
      congr 1
      simp only [esum_add, esum_sub]
      ring

/-- A sum over `Idx` of a function supported on two points. -/
lemma sum_pair_support {N : Type*} [AddCommMonoid N] (f : Idx → N) {P Q : Idx} (hPQ : P ≠ Q)
    (h0 : ∀ z, z ≠ P → z ≠ Q → f z = 0) : ∑ z : Idx, f z = f P + f Q := by
  classical
  rw [← Finset.sum_pair hPQ]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro z _ hz
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  exact h0 z hz.1 hz.2

/-- `L` evaluated on a key difference supported on two words. -/
lemma L_sparse (w : A) (ι : R →+ M) (d y : Idx → R) {P Q : Idx} (hPQ : P ≠ Q)
    (hy : ∀ z, z ≠ P → z ≠ Q → y z = 0) :
    L w ι d y = (ι (d (P.1, sw P.2) * y P) + ι (d (Q.1, sw Q.2) * y Q),
      (beta w P.1 • ι (d (P.1, sw P.2) * y P) + beta w Q.1 • ι (d (Q.1, sw Q.2) * y Q))
        + (ι (esum d (sw P.2) * y P) + ι (esum d (sw Q.2) * y Q))) := by
  have h1 := sum_pair_support (fun z : Idx => ι (d (z.1, sw z.2) * y z)) hPQ
    (fun z hp hq => by simp [hy z hp hq])
  have h2 := sum_pair_support (fun z : Idx => beta w z.1 • ι (d (z.1, sw z.2) * y z)) hPQ
    (fun z hp hq => by simp [hy z hp hq])
  have h3 := sum_pair_support (fun z : Idx => ι (esum d (sw z.2) * y z)) hPQ
    (fun z hp hq => by simp [hy z hp hq])
  rw [L, h1, h2, h3]

end Hash

/-! ### The main theorem -/

section Main

/-- The 64-bit words: polynomials of degree `< 64`. -/
noncomputable abbrev Wd : Submodule (ZMod 2) R := Polynomial.degreeLT (ZMod 2) 64

lemma degree_lt_64 (x : Wd) : (x : R).degree < 64 := Polynomial.mem_degreeLT.mp x.2

variable {M : Type*} [AddCommGroup M] {A : Type*} [CommRing A] [CharP A 2] [Module A M]

/-- For any nonzero input difference there are two words, in different
arguments, on which the linear part `L` of the difference is injective. -/
theorem exists_pivot (w : A) (hw : w ^ 2 = w + 1) (ι : R →+ M)
    (hι : ∀ x : R, x.degree < 128 → ι x = 0 → x = 0)
    (d : Idx → R) (hd64 : ∀ z, (d z).degree < 64) (hd : d ≠ 0) :
    ∃ P Q : Idx, P ≠ Q ∧ ∀ y : Idx → R, (∀ z, (y z).degree < 64) →
      (∀ z, z ≠ P → z ≠ Q → y z = 0) → L w ι d y = 0 → y = 0 := by
  have hne : ∀ (i j : Fin 4) (l l' : Fin 2), i ≠ j → ((i, l) : Idx) ≠ (j, l') := by
    intro i j l l' hij h
    exact hij (congrArg Prod.fst h)
  -- packaging: from the two pivot words being zero, the whole difference is zero
  have hfun : ∀ (P Q : Idx) (y : Idx → R), (∀ z, z ≠ P → z ≠ Q → y z = 0) →
      y P = 0 → y Q = 0 → y = 0 := by
    intro P Q y hsupp hP hQ
    funext z
    by_cases h1 : z = P
    · rw [h1]; exact hP
    by_cases h2 : z = Q
    · rw [h2]; exact hQ
    · exact hsupp z h1 h2
  by_cases hE : ∀ l : Fin 2, esum d l = 0
  · -- Case A: `e = 0`. Two arguments have a nonzero difference.
    obtain ⟨⟨i, σ⟩, hz0⟩ := Function.ne_iff.mp hd
    simp only [Pi.zero_apply] at hz0
    obtain ⟨j, τ, hji, hjτ⟩ : ∃ j τ, j ≠ i ∧ d (j, τ) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hs : esum d σ = d (i, σ) :=
        Finset.sum_eq_single i (fun k _ hk => hcon k σ hk) (by simp)
      rw [hE σ] at hs
      exact hz0 hs.symm
    have hPQ : ((i, sw σ) : Idx) ≠ (j, sw τ) := hne i j _ _ (Ne.symm hji)
    refine ⟨(i, sw σ), (j, sw τ), hPQ, ?_⟩
    intro y hy64 hsupp hL
    rw [L_sparse w ι d y hPQ hsupp] at hL
    rw [Prod.ext_iff] at hL
    obtain ⟨h0, h1⟩ := hL
    simp only [Prod.fst_zero, Prod.snd_zero, sw_sw, hE, zero_mul, map_zero, add_zero] at h0 h1
    obtain ⟨hu, hv⟩ := two_word_caseA ι hι hz0 hjτ (hd64 _) (hd64 _)
      (hy64 _) (hy64 _) (isUnit_beta_sub hw (Ne.symm hji)) h0 h1
    exact hfun _ _ y hsupp hu hv
  · -- Case B: `e ≠ 0`. One of the two `β`-pairs has a nonzero determinant.
    push Not at hE
    obtain ⟨σ, hσ⟩ := hE
    have hεd : (esum d σ).degree < 64 := by
      simp only [esum]
      exact Polynomial.mem_degreeLT.mp
        (Submodule.sum_mem _ fun k _ => Polynomial.mem_degreeLT.mpr (hd64 (k, σ)))
    -- a pair `(i, j)` that works
    have pivot : ∀ i j : Fin 4, i ≠ j → beta w i + beta w j = 1 →
        d (i, σ) * esum d σ + d (j, σ) * esum d σ + d (i, σ) * d (j, σ) ≠ 0 →
        ∃ P Q : Idx, P ≠ Q ∧ ∀ y : Idx → R, (∀ z, (y z).degree < 64) →
          (∀ z, z ≠ P → z ≠ Q → y z = 0) → L w ι d y = 0 → y = 0 := by
      intro i j hij hβ hdet
      have hPQ : ((i, sw σ) : Idx) ≠ (j, sw σ) := hne i j _ _ hij
      refine ⟨(i, sw σ), (j, sw σ), hPQ, ?_⟩
      intro y hy64 hsupp hL
      rw [L_sparse w ι d y hPQ hsupp] at hL
      rw [Prod.ext_iff] at hL
      obtain ⟨h0, h1⟩ := hL
      simp only [Prod.fst_zero, Prod.snd_zero, sw_sw] at h0 h1
      obtain ⟨hu, hv⟩ := two_word_caseB ι hι (hd64 _) (hd64 _) hεd
        (hy64 _) (hy64 _) hβ hdet h0 h1
      exact hfun _ _ y hsupp hu hv
    -- the excluded system rules out both determinants vanishing
    have hdet : d (0, σ) * esum d σ + d (1, σ) * esum d σ + d (0, σ) * d (1, σ) ≠ 0 ∨
        d (2, σ) * esum d σ + d (3, σ) * esum d σ + d (2, σ) * d (3, σ) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h01, h23⟩ := hcon
      refine no_excluded_system (a := d (0, σ)) (b := d (1, σ)) (c := d (2, σ))
        (d := d (3, σ)) (e := esum d σ) ?_ hσ ?_ ?_
      · simp [esum, Fin.sum_univ_four]
      · linear_combination₂ h01
      · linear_combination₂ h23
    rcases hdet with h | h
    · exact pivot 0 1 (by decide) beta_pair01 h
    · exact pivot 2 3 (by decide) (beta_pair23 hw) h

/-! ### Counting -/

lemma card_pivot_le {V : Type*} [Finite V] {T : Type*} (F : (Idx → V) → T) (t : T)
    {P Q : Idx} (hPQ : P ≠ Q)
    (hinj : ∀ K K' : Idx → V, F K = t → F K' = t →
      (∀ z, z ≠ P → z ≠ Q → K z = K' z) → K = K') :
    Nat.card {K : Idx → V // F K = t} ≤ Nat.card V ^ 6 := by
  classical
  have hsub : Nat.card {z : Idx // z ≠ P ∧ z ≠ Q} = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h : (Finset.univ.filter (fun z : Idx => z ≠ P ∧ z ≠ Q)) = Finset.univ \ {P, Q} := by
      ext z; simp
    rw [h, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Finset.card_insert_of_notMem (by simpa using hPQ), Finset.card_singleton]
    rfl
  have hcard : Nat.card ({z : Idx // z ≠ P ∧ z ≠ Q} → V) = Nat.card V ^ 6 := by
    rw [Nat.card_fun, hsub]
  rw [← hcard]
  refine Nat.card_le_card_of_injective (fun K z => K.1 z.1) ?_
  rintro ⟨K, hK⟩ ⟨K', hK'⟩ h
  refine Subtype.ext (hinj K K' hK hK' ?_)
  intro z h1 h2
  exact congrFun h ⟨z, h1, h2⟩

instance : Finite (Wd : Type) :=
  Finite.of_equiv (Fin 64 → ZMod 2) (Polynomial.degreeLTEquiv (ZMod 2) 64).toEquiv.symm

lemma card_Wd : Nat.card (Wd : Type) = 2 ^ 64 := by
  rw [Nat.card_congr (Polynomial.degreeLTEquiv (ZMod 2) 64).toEquiv, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- For any nonzero input difference `δ` and any output difference `γ`, at most
a `2⁻¹²⁸` fraction of the `2⁵¹²` keys `K` have `H (K + δ) - H K = γ`. -/
theorem card_diff_le (w : A) (hw : w ^ 2 = w + 1) (ι : R →+ M)
    (hι : ∀ x : R, x.degree < 128 → ι x = 0 → x = 0)
    (δ : Idx → Wd) (hδ : δ ≠ 0) (γ : M × M) :
    Nat.card {K : Idx → Wd // D w ι (fun z => (δ z : R)) (fun z => (K z : R)) = γ} * 2 ^ 128
      ≤ Nat.card (Idx → Wd) := by
  set d : Idx → R := fun z => (δ z : R) with hdd
  have hd64 : ∀ z, (d z).degree < 64 := fun z => degree_lt_64 (δ z)
  have hd : d ≠ 0 := by
    obtain ⟨z, hz⟩ := Function.ne_iff.mp hδ
    exact Function.ne_iff.mpr ⟨z, by simpa [hdd] using fun h => hz (Subtype.ext h)⟩
  obtain ⟨P, Q, hPQ, hpiv⟩ := exists_pivot w hw ι hι d hd64 hd
  have hbound : Nat.card {K : Idx → Wd // D w ι d (fun z => (K z : R)) = γ}
      ≤ Nat.card (Wd : Type) ^ 6 := by
    refine card_pivot_le (V := (Wd : Type)) (fun K => D w ι d (fun z => (K z : R))) γ hPQ ?_
    intro K K' hK hK' hagree
    have hy : (fun z => (K z : R)) - (fun z => (K' z : R)) = 0 := by
      refine hpiv _ (fun z => ?_) (fun z h1 h2 => ?_) ?_
      · exact Polynomial.mem_degreeLT.mp (Submodule.sub_mem _ (K z).2 (K' z).2)
      · simp [hagree z h1 h2]
      · rw [← D_sub, hK, hK', sub_self]
    funext z
    have := congrFun hy z
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact Subtype.ext this
  calc Nat.card {K : Idx → Wd // D w ι d (fun z => (K z : R)) = γ} * 2 ^ 128
      ≤ Nat.card (Wd : Type) ^ 6 * 2 ^ 128 := Nat.mul_le_mul_right _ hbound
    _ = Nat.card (Idx → Wd) := by
        rw [Nat.card_fun, card_Wd, Nat.card_eq_fintype_card (α := Idx)]
        norm_num [← pow_mul, ← pow_add]

end Main

end PolyXOR.CompressProof
