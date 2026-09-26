import Mathlib

/-!
# The excluded system

This file proves the polynomial identity that Case B of `exists_pivot` in
`PolyXOR.CompressProof.Core` relies on:

> There are no `a, b, c, d ∈ 𝔽₂[X]` with `e = a + b + c + d ≠ 0`,
> `a b = e (a + b)` and `c d = e (c + d)`.

In characteristic two, `a b = e (a + b)` says that the determinant
`a e + b e + a b` vanishes, so this states that the determinants for the pairs
`{a, b}` and `{c, d}` cannot both vanish.

The argument uses unique factorization in `𝔽₂[X]`. That is why the carryless
products must not be reduced modulo a polynomial: in the quotient ring there
are zero divisors and the argument breaks.

## Outline

Write `N p q = p² + p q + q²`. In characteristic two, `N p q = p q + (p + q)²`.

1. `step_one`: none of `a, b, c, d` is zero. If `a = 0` then `b = 0`, so
   `N c d = 0`, which forces `c = d = 0` (`eq_zero_of_N_eq_zero`) and `e = 0`.
2. `param`: reduce each pair to lowest terms. With `a = g p`, `b = g q`, `p` and
   `q` coprime and `r = p + q`, the identity `a b = e (a + b)` forces `r ∣ g`.
   Writing `g = h r` gives `e = h p q` and `a + b = h r²`.
3. Substituting into `e = (a + b) + (c + d)` gives `h N p q = k r'²` and
   `k N p' q' = h r²`. `N p q` is coprime to `r`, so `N p q ∣ r'²` and
   `N p' q' ∣ r²`. Comparing degrees, and using that every nonzero polynomial
   over `𝔽₂` is monic, `N p q = r'²` and `N p' q' = r²`.
4. `not_admissible`: infinite descent. A polynomial over `𝔽₂` is a square iff
   its derivative is zero, and `(N p q)' = p' q + p q'`. With `p`, `q` coprime
   this shows `p` and `q` are squares whenever `N p q` is. Taking square roots of
   `p, q, p', q'` halves their degrees and keeps the identities of step 3, so
   by induction we reach degree `0`, where `p = q = 1`, contradicting `p ≠ q`.
-/

namespace PolyXOR.CompressProof

open Polynomial

/-- The ring `𝔽₂[X]`, in which the unreduced carryless products live. -/
abbrev R : Type := Polynomial (ZMod 2)

/-- Numerals in `𝔽₂[X]` reduce modulo `2`. Used by `linear_combination₂`. -/
lemma ofNat_eq_mod (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : R) = ((n % 2 : ℕ) : R) := by
  rw [← CharP.cast_eq_mod R 2 n]; rfl

/-- `linear_combination` in `𝔽₂[X]`: numerals are reduced modulo `2`, so
multiples of `2` vanish. -/
syntax "linear_combination₂" (ppSpace colGt term)? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| linear_combination₂ $e:term) =>
    `(tactic| linear_combination
      (norm := first | ring1 | (ring_nf; simp [PolyXOR.CompressProof.ofNat_eq_mod])) $e:term)
  | `(tactic| linear_combination₂) =>
    `(tactic| linear_combination
      (norm := first | ring1 | (ring_nf; simp [PolyXOR.CompressProof.ofNat_eq_mod])))

/-! ### Basic facts about `𝔽₂[X]` -/

/-- A nonzero constant polynomial over `𝔽₂` is `1`. -/
lemma eq_one_of_natDegree_eq_zero {p : R} (hp : p ≠ 0) (h : p.natDegree = 0) : p = 1 := by
  obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h
  have ha : a ≠ 0 := by rintro rfl; simp at hp
  have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  rw [this a ha, map_one]

/-- Over `𝔽₂` the only unit polynomial is `1`. -/
lemma isUnit_iff_eq_one {p : R} : IsUnit p ↔ p = 1 :=
  ⟨fun h => eq_one_of_natDegree_eq_zero h.ne_zero (natDegree_eq_zero_of_isUnit h),
    fun h => h ▸ isUnit_one⟩

/-- Over `𝔽₂` every nonzero polynomial is monic, so a divisor of the same
degree is equal. -/
lemma eq_of_dvd_of_natDegree_le {u v : R} (hv : v ≠ 0) (hdvd : u ∣ v)
    (hdeg : v.natDegree ≤ u.natDegree) : u = v := by
  obtain ⟨w, rfl⟩ := hdvd
  have hu : u ≠ 0 := by rintro rfl; simp at hv
  have hw : w ≠ 0 := by rintro rfl; simp at hv
  rw [natDegree_mul hu hw] at hdeg
  rw [eq_one_of_natDegree_eq_zero hw (by omega), mul_one]

/-- If `p` and `q` are coprime, `p + q` is coprime to `p q`. -/
lemma isCoprime_add_mul {p q : R} (hpq : IsCoprime p q) : IsCoprime (p + q) (p * q) := by
  have hp : IsCoprime (p + q) p := by
    simpa [add_comm q p] using hpq.symm.add_mul_left_left 1
  have hq : IsCoprime (p + q) q := by
    simpa using hpq.add_mul_left_left 1
  exact hp.mul_right hq

/-! ### Squares in characteristic two -/

/-- A polynomial over `𝔽₂` with vanishing derivative is a square. -/
lemma exists_sq_of_derivative_eq_zero {f : R} (hf : derivative f = 0) :
    ∃ g : R, f = g ^ 2 := by
  refine ⟨contract 2 f, ?_⟩
  have h := map_frobenius_expand (R := ZMod 2) (p := 2) (contract 2 f)
  rwa [ZMod.frobenius_zmod, map_id, expand_contract 2 hf two_ne_zero] at h

/-- The norm form `N p q = p² + p q + q²`. -/
noncomputable def N (p q : R) : R := p ^ 2 + p * q + q ^ 2

lemma N_comm (p q : R) : N p q = N q p := by unfold N; ring

/-- In characteristic two, `N p q = p q + (p + q)²`. -/
lemma N_eq_add_sq (p q : R) : N p q = p * q + (p + q) ^ 2 := by
  unfold N; linear_combination₂

/-- Squaring is the Frobenius, so it commutes with `N`. -/
lemma N_sq (P Q : R) : N (P ^ 2) (Q ^ 2) = N P Q ^ 2 := by
  unfold N; linear_combination₂

lemma derivative_N (p q : R) :
    derivative (N p q) = derivative p * q + p * derivative q := by
  unfold N
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  simp only [map_add, derivative_mul, derivative_pow, h2, map_zero]
  ring

/-- If `p` and `q` are coprime and `N p q` is a square, then `p` is a square. -/
lemma exists_sq_left_of_isCoprime {p q : R} (hpq : IsCoprime p q) {t : R}
    (ht : N p q = t ^ 2) : ∃ P : R, p = P ^ 2 := by
  have hder : derivative p * q = p * derivative q := by
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    have h := derivative_N p q
    rw [ht, derivative_pow, h2, map_zero, zero_mul, zero_mul, eq_comm,
      CharTwo.add_eq_zero] at h
    exact h
  have hp' : p ∣ derivative p := hpq.dvd_of_dvd_mul_right (hder ▸ dvd_mul_right _ _)
  refine exists_sq_of_derivative_eq_zero (by_contra fun hne => ?_)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hne
  exact absurd (degree_le_of_dvd hp' hne) (not_le.mpr (degree_derivative_lt hp0))

lemma exists_sq_right_of_isCoprime {p q : R} (hpq : IsCoprime p q) {t : R}
    (ht : N p q = t ^ 2) : ∃ Q : R, q = Q ^ 2 :=
  exists_sq_left_of_isCoprime hpq.symm (by rw [N_comm]; exact ht)

/-! ### `N p q = 0` has only the trivial solution -/

lemma eq_zero_of_N_eq_zero {c d : R} (h : N c d = 0) : c = 0 ∧ d = 0 := by
  by_cases hc : c = 0
  · subst hc
    have : d ^ 2 = 0 := by unfold N at h; linear_combination h
    exact ⟨rfl, pow_eq_zero_iff two_ne_zero |>.mp this⟩
  · exfalso
    -- Divide out `g = gcd c d`; then `N c₁ d₁ = 0` with `c₁`, `d₁` coprime.
    set g := GCDMonoid.gcd c d
    have hg0 : g ≠ 0 := fun h0 => hc ((gcd_eq_zero_iff c d).mp h0).1
    set c₁ := c / g
    set d₁ := d / g
    have hcc : g * c₁ = c := EuclideanDomain.mul_div_cancel' hg0 (GCDMonoid.gcd_dvd_left c d)
    have hdd : g * d₁ = d := EuclideanDomain.mul_div_cancel' hg0 (GCDMonoid.gcd_dvd_right c d)
    have hcop : IsCoprime c₁ d₁ := isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
    have hN0 : N c₁ d₁ = 0 := by
      have : g ^ 2 * N c₁ d₁ = 0 := by rw [← h]; unfold N; rw [← hcc, ← hdd]; ring
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hg0)
    -- `d₁ ∣ c₁²` and `c₁ ∣ d₁²`, so by coprimality both are units, i.e. `1`.
    have hdvd_d : d₁ ∣ c₁ ^ 2 := ⟨c₁ + d₁, by unfold N at hN0; linear_combination₂ hN0⟩
    have hdvd_c : c₁ ∣ d₁ ^ 2 := ⟨c₁ + d₁, by unfold N at hN0; linear_combination₂ hN0⟩
    have hud : IsUnit d₁ := hcop.pow_left.isUnit_of_dvd' hdvd_d dvd_rfl
    have huc : IsUnit c₁ := hcop.symm.pow_left.isUnit_of_dvd' hdvd_c dvd_rfl
    rw [isUnit_iff_eq_one.mp huc, isUnit_iff_eq_one.mp hud] at hN0
    unfold N at hN0
    exact one_ne_zero (α := R) (by linear_combination₂ hN0)

/-! ### The descent -/

/-- The shape left over after reducing both pairs to lowest terms.
The descent below shows no such quadruple exists. -/
structure Admissible (p q p' q' : R) : Prop where
  cop : IsCoprime p q
  cop' : IsCoprime p' q'
  p_ne : p ≠ 0
  q_ne : q ≠ 0
  ne : p ≠ q
  hN : N p q = (p' + q') ^ 2
  hN' : N p' q' = (p + q) ^ 2

theorem not_admissible : ∀ (n : ℕ) (p q p' q' : R),
    p.natDegree + q.natDegree + p'.natDegree + q'.natDegree = n →
    ¬ Admissible p q p' q' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q p' q' hn hA
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · -- All four are constants, so `p = q = 1`.
      exact hA.ne (by
        rw [eq_one_of_natDegree_eq_zero hA.p_ne (by omega),
          eq_one_of_natDegree_eq_zero hA.q_ne (by omega)])
    · -- All four are squares; pass to the square roots, halving all degrees.
      obtain ⟨P, rfl⟩ := exists_sq_left_of_isCoprime hA.cop hA.hN
      obtain ⟨Q, rfl⟩ := exists_sq_right_of_isCoprime hA.cop hA.hN
      obtain ⟨P', rfl⟩ := exists_sq_left_of_isCoprime hA.cop' hA.hN'
      obtain ⟨Q', rfl⟩ := exists_sq_right_of_isCoprime hA.cop' hA.hN'
      have hNPQ : N P Q = (P' + Q') ^ 2 := by
        rw [← CharTwo.sq_inj, ← N_sq, hA.hN, ← CharTwo.add_sq]
      have hNPQ' : N P' Q' = (P + Q) ^ 2 := by
        rw [← CharTwo.sq_inj, ← N_sq, hA.hN', ← CharTwo.add_sq]
      simp only [natDegree_pow] at hn
      refine ih (P.natDegree + Q.natDegree + P'.natDegree + Q'.natDegree) (by omega)
        P Q P' Q' rfl ⟨IsCoprime.pow_iff two_pos two_pos |>.mp hA.cop,
          IsCoprime.pow_iff two_pos two_pos |>.mp hA.cop', ?_, ?_, ?_, hNPQ, hNPQ'⟩
      · exact fun h => hA.p_ne (by rw [h]; ring)
      · exact fun h => hA.q_ne (by rw [h]; ring)
      · exact fun h => hA.ne (by rw [h])

/-! ### Reduction to lowest terms -/

/-- Step 2. If `a b = e (a + b)` with `a, b` nonzero, then in lowest terms
`a = g r p`, `b = g r q` with `r = p + q` coprime to `p q`, and consequently
`e = g p q` and `a + b = g r²`. Only the last two identities are used later. -/
lemma param {a b e : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a * b = e * (a + b)) :
    ∃ g p q : R, IsCoprime p q ∧ p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ g ≠ 0 ∧
      e = g * (p * q) ∧ a + b = g * (p + q) ^ 2 := by
  -- Divide out `g₀ = gcd a b`.
  have hgcd : GCDMonoid.gcd a b ≠ 0 := fun h0 => ha ((gcd_eq_zero_iff a b).mp h0).1
  obtain ⟨g₀, p, q, hg₀, hp, hq, hcop, rfl, rfl⟩ :
      ∃ g₀ p q : R, g₀ ≠ 0 ∧ p ≠ 0 ∧ q ≠ 0 ∧ IsCoprime p q ∧ a = g₀ * p ∧ b = g₀ * q :=
    ⟨_, _, _, hgcd, left_div_gcd_ne_zero ha, right_div_gcd_ne_zero hb,
      isCoprime_div_gcd_div_gcd hb,
      (EuclideanDomain.mul_div_cancel' hgcd (GCDMonoid.gcd_dvd_left a b)).symm,
      (EuclideanDomain.mul_div_cancel' hgcd (GCDMonoid.gcd_dvd_right a b)).symm⟩
  have hr : p + q ≠ 0 := by
    intro h0
    rw [← mul_add, h0, mul_zero, mul_zero] at h
    simp_all
  -- Cancelling `g₀` gives `g₀ p q = e (p + q)`, so `p + q ∣ g₀`.
  have key : g₀ * (p * q) = e * (p + q) :=
    mul_left_cancel₀ hg₀ (by linear_combination h)
  obtain ⟨g, rfl⟩ : (p + q) ∣ g₀ :=
    (isCoprime_add_mul hcop).dvd_of_dvd_mul_right ⟨e, by rw [key]; ring⟩
  have hg : g ≠ 0 := by rintro rfl; simp at hg₀
  refine ⟨g, p, q, hcop, hp, hq, fun h0 => hr (by rw [h0]; exact CharTwo.add_self_eq_zero q),
    hg, (mul_left_cancel₀ hr (by linear_combination key)).symm, by ring⟩

/-! ### The excluded system -/

/-- Step 1: none of `a, b, c, d` is zero. -/
lemma step_one {a b c d e : R} (hea : e = a + b + c + d) (he : e ≠ 0)
    (hab : a * b = e * (a + b)) (hcd : c * d = e * (c + d)) (ha : a = 0) : False := by
  subst ha
  have hb : b = 0 := by simpa [he] using hab.symm
  subst hb
  -- Now `e = c + d` and `c d = (c + d)²`, i.e. `N c d = 0`.
  have hecd : e = c + d := by rw [hea]; ring
  have hN : N c d = 0 := by rw [N_eq_add_sq, hcd, hecd]; linear_combination₂
  obtain ⟨rfl, rfl⟩ := eq_zero_of_N_eq_zero hN
  exact he (by rw [hecd, add_zero])

/-- `N p q` is coprime to `(p + q)²`: modulo `p + q` it is `p q`. -/
lemma isCoprime_N_sq {p q : R} (hcop : IsCoprime p q) :
    IsCoprime (N p q) ((p + q) ^ 2) := by
  have h := (isCoprime_add_mul hcop).add_mul_left_right (p + q)
  rw [← sq, ← N_eq_add_sq] at h
  exact h.symm.pow_right

/-- There are no `a, b, c, d ∈ 𝔽₂[X]` with
`e := a + b + c + d ≠ 0`, `a b = e (a + b)` and `c d = e (c + d)`. -/
theorem no_excluded_system {a b c d e : R} (hea : e = a + b + c + d) (he : e ≠ 0)
    (hab : a * b = e * (a + b)) (hcd : c * d = e * (c + d)) : False := by
  -- Step 1: `a, b, c, d` are nonzero.
  have ha : a ≠ 0 := step_one hea he hab hcd
  have hb : b ≠ 0 := step_one (a := b) (b := a) (by rw [hea]; ring) he
    (by linear_combination hab) hcd
  have hc : c ≠ 0 := step_one (a := c) (b := d) (c := a) (d := b) (by rw [hea]; ring) he hcd hab
  have hd : d ≠ 0 := step_one (a := d) (b := c) (c := a) (d := b) (by rw [hea]; ring) he
    (by linear_combination hcd) hab
  -- Step 2: reduce both pairs to lowest terms.
  obtain ⟨g, p, q, hcop, hp, hq, hpq, hg, hge, hgab⟩ := param ha hb hab
  obtain ⟨k, p', q', hcop', hp', hq', hpq', hk, hke, hkcd⟩ := param hc hd hcd
  have hsum : e = g * (p + q) ^ 2 + k * (p' + q') ^ 2 := by
    rw [← hgab, ← hkcd, hea]; ring
  -- Step 3: two square identities, multiplied together to cancel `g k`.
  have hgN : g * N p q = k * (p' + q') ^ 2 := by
    rw [N_eq_add_sq]; linear_combination₂ hsum - hge
  have hkN : k * N p' q' = g * (p + q) ^ 2 := by
    rw [N_eq_add_sq]; linear_combination₂ hsum - hke
  have hr : (p + q) ^ 2 ≠ 0 := pow_ne_zero 2 fun h0 => hpq (CharTwo.add_eq_zero.mp h0)
  have hr' : (p' + q') ^ 2 ≠ 0 := pow_ne_zero 2 fun h0 => hpq' (CharTwo.add_eq_zero.mp h0)
  have hprod : N p q * N p' q' = (p + q) ^ 2 * (p' + q') ^ 2 :=
    mul_left_cancel₀ (mul_ne_zero hg hk) (by linear_combination k * N p' q' * hgN + k * (p' + q') ^ 2 * hkN)
  have hN0 : N p q ≠ 0 := by rintro h0; simp [h0, hr, hr'] at hprod
  have hN0' : N p' q' ≠ 0 := by rintro h0; simp [h0, hr, hr'] at hprod
  have hdvd : N p q ∣ (p' + q') ^ 2 :=
    (isCoprime_N_sq hcop).dvd_of_dvd_mul_left ⟨N p' q', hprod.symm⟩
  have hdvd' : N p' q' ∣ (p + q) ^ 2 :=
    (isCoprime_N_sq hcop').dvd_of_dvd_mul_left ⟨N p q, by linear_combination -hprod⟩
  -- The two divisibilities have degrees summing to the total, so both are equalities.
  have hdeg1 := natDegree_le_of_dvd hdvd hr'
  have hdeg2 := natDegree_le_of_dvd hdvd' hr
  have hdegsum := congrArg natDegree hprod
  rw [natDegree_mul hN0 hN0', natDegree_mul hr hr'] at hdegsum
  exact not_admissible _ p q p' q' rfl
    ⟨hcop, hcop', hp, hq, hpq,
      eq_of_dvd_of_natDegree_le hr' hdvd (by omega),
      eq_of_dvd_of_natDegree_le hr hdvd' (by omega)⟩

end PolyXOR.CompressProof
