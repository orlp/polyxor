import Mathlib

/-!
# Counting solutions over a finite field
-/

namespace PolyXOR.FullProof

open Polynomial

/-- Counting a subtype of a product fiberwise. -/
theorem card_prod_subtype {α β : Type*} [Finite α] [Finite β] (P : α × β → Prop) :
    Nat.card {p : α × β // P p} = ∑ᶠ a : α, Nat.card {b : β // P (a, b)} := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

variable {F : Type*} [Field F] [Finite F]

/-- A field of size `2¹²⁸` has characteristic two. -/
theorem charP_two_of_card (hF : Nat.card F = 2 ^ 128) : CharP F 2 := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card, hF] at hn
  have h2 : ringChar F ∣ 2 := hp.dvd_of_dvd_pow (n := 128) (hn ▸ dvd_pow_self _ n.ne_zero)
  exact ringChar.eq_iff.mp ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

omit [Field F] in
/-- Counting triples `(z, u, y)` fiberwise over `y`. -/
theorem card_triple_eq_sum [Fintype F] (P : F → F → F → Prop) :
    Nat.card {t : F × F × F // P t.1 t.2.1 t.2.2}
      = ∑ y : F, Nat.card {p : F × F // P p.1 p.2 y} := by
  let e : {t : F × F × F // P t.1 t.2.1 t.2.2} ≃ {p : F × (F × F) // P p.2.1 p.2.2 p.1} :=
    { toFun := fun t => ⟨(t.1.2.2, (t.1.1, t.1.2.1)), t.2⟩
      invFun := fun p => ⟨(p.1.2.1, p.1.2.2, p.1.1), p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_prod_subtype, finsum_eq_sum_of_fintype]

omit [Field F] in
/-- A subtype of `F × F` has at most `q²` elements. -/
theorem card_pair_subtype_le (Q : F × F → Prop) : Nat.card {p : F × F // Q p} ≤ Nat.card F ^ 2 :=
  (Finite.card_subtype_le _).trans (by rw [Nat.card_prod, sq])

omit [Finite F] in
/-- Summing a bound that is `q` off the roots of `g` and `q²` on them. -/
theorem sum_le_of_roots [Fintype F] (g : F[X]) (hg : g ≠ 0) {d : ℕ} (hd : g.natDegree ≤ d)
    (c : F → ℕ) (hc : ∀ y, c y ≤ Nat.card F ^ 2) (hc' : ∀ y, g.eval y ≠ 0 → c y ≤ Nat.card F) :
    ∑ y : F, c y ≤ (d + 1) * Nat.card F ^ 2 := by
  classical
  set R := g.roots.toFinset
  have hR : R.card ≤ d := (Multiset.toFinset_card_le _).trans ((card_roots' g).trans hd)
  calc ∑ y : F, c y ≤ ∑ y : F, (Nat.card F + if y ∈ R then Nat.card F ^ 2 else 0) := by
        refine Finset.sum_le_sum fun y _ => ?_
        split_ifs with hy
        · exact (hc y).trans (Nat.le_add_left _ _)
        · refine (hc' y fun h => hy ?_).trans (Nat.le_add_right _ _)
          exact Multiset.mem_toFinset.mpr ((mem_roots hg).mpr h)
    _ = Nat.card F * Nat.card F + R.card * Nat.card F ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul,
          smul_eq_mul]
    _ ≤ (d + 1) * Nat.card F ^ 2 := by
        rw [add_mul, one_mul, add_comm, ← sq]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hR) _

/-- The number of `(z, u, y)` with `g₁(y) + z g₂(y) + u g₃(y) = γ`, when `g₂ ≠ 0`. -/
theorem card_solutions_le_of_g2 (g₁ g₂ g₃ : F[X]) (γ : F) (h₂ : g₂ ≠ 0) {d : ℕ}
    (hd : g₂.natDegree ≤ d) :
    Nat.card {t : F × F × F //
        g₁.eval t.2.2 + t.1 * g₂.eval t.2.2 + t.2.1 * g₃.eval t.2.2 = γ}
      ≤ (d + 1) * Nat.card F ^ 2 := by
  have := Fintype.ofFinite F
  rw [card_triple_eq_sum (fun z u y => g₁.eval y + z * g₂.eval y + u * g₃.eval y = γ)]
  refine sum_le_of_roots g₂ h₂ hd _ (fun _ => card_pair_subtype_le _) fun y hy => ?_
  refine Nat.card_le_card_of_injective (fun p => p.1.2) ?_
  rintro ⟨⟨z, u⟩, hp⟩ ⟨⟨z', u'⟩, hq⟩ (rfl : u = u')
  simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true]
  exact mul_right_cancel₀ hy (by linear_combination hp - hq)

/-- The number of `(z, u, y)` with `g₁(y) + z g₂(y) + u g₃(y) = γ`, when `g₃ ≠ 0`. -/
theorem card_solutions_le_of_g3 (g₁ g₂ g₃ : F[X]) (γ : F) (h₃ : g₃ ≠ 0) {d : ℕ}
    (hd : g₃.natDegree ≤ d) :
    Nat.card {t : F × F × F //
        g₁.eval t.2.2 + t.1 * g₂.eval t.2.2 + t.2.1 * g₃.eval t.2.2 = γ}
      ≤ (d + 1) * Nat.card F ^ 2 := by
  have := Fintype.ofFinite F
  rw [card_triple_eq_sum (fun z u y => g₁.eval y + z * g₂.eval y + u * g₃.eval y = γ)]
  refine sum_le_of_roots g₃ h₃ hd _ (fun _ => card_pair_subtype_le _) fun y hy => ?_
  refine Nat.card_le_card_of_injective (fun p => p.1.1) ?_
  rintro ⟨⟨z, u⟩, hp⟩ ⟨⟨z', u'⟩, hq⟩ (rfl : z = z')
  simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
  exact mul_right_cancel₀ hy (by linear_combination hp - hq)

/-- The number of `(z, u, y)` with `g₁(y) = γ`, when `g₁ - γ ≠ 0`. -/
theorem card_solutions_le_of_g1 (g₁ : F[X]) (γ : F) (h₁ : g₁ - C γ ≠ 0) {d : ℕ}
    (hd : (g₁ - C γ).natDegree ≤ d) :
    Nat.card {t : F × F × F // g₁.eval t.2.2 = γ} ≤ d * Nat.card F ^ 2 := by
  classical
  have := Fintype.ofFinite F
  set R := (g₁ - C γ).roots.toFinset
  have hR : R.card ≤ d := (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hd)
  rw [card_triple_eq_sum (fun _ _ y => g₁.eval y = γ)]
  calc ∑ y : F, Nat.card {p : F × F // g₁.eval y = γ}
      ≤ ∑ y : F, if y ∈ R then Nat.card F ^ 2 else 0 := by
        refine Finset.sum_le_sum fun y _ => ?_
        split_ifs with hy
        · exact card_pair_subtype_le _
        · refine (Nat.card_eq_zero.mpr (Or.inl ⟨fun p => hy ?_⟩)).le
          refine Multiset.mem_toFinset.mpr ((mem_roots h₁).mpr ?_)
          simp [p.2]
    _ = R.card * Nat.card F ^ 2 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
    _ ≤ d * Nat.card F ^ 2 := Nat.mul_le_mul_right _ hR

end PolyXOR.FullProof
