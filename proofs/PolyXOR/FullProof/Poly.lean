import PolyXOR.FullProof.Recurrence
import PolyXOR.FullProof.Count

/-!
# The polynomial stage

For fixed distinct pair sequences, few keys `(z, u, y)` make the accumulators
differ by `γ`.
-/

namespace PolyXOR.FullProof

open Polynomial

variable {F : Type*} [Field F]

/-- The accumulators differ by `γ` iff the coefficient differences solve the
affine equation counted in `Count`. -/
lemma accum_eq_add_iff (s s' : List (F × F)) (γ : F) (t : F × F × F) :
    accum t.1 t.2.1 t.2.2 s = accum t.1 t.2.1 t.2.2 s' + γ ↔
      ((coeffs s).1 - (coeffs s').1).eval t.2.2
        + t.1 * ((coeffs s).2.1 - (coeffs s').2.1).eval t.2.2
        + t.2.1 * ((coeffs s).2.2 - (coeffs s').2.2).eval t.2.2 = γ := by
  rw [accum_eq, accum_eq]
  simp only [eval_sub]
  constructor <;> intro h <;> linear_combination h

variable [Finite F]

theorem card_accum_le_of_length_eq {s s' : List (F × F)} (γ : F) (hlen : s.length = s'.length)
    (hs : s ≠ []) (hne : s ≠ s')
    (hlast : (s.getLast?).map Prod.fst = (s'.getLast?).map Prod.fst) :
    Nat.card {t : F × F × F // accum t.1 t.2.1 t.2.2 s = accum t.1 t.2.1 t.2.2 s' + γ}
      ≤ s.length * Nat.card F ^ 2 := by
  have hn : 1 ≤ s.length := List.length_pos_iff.mpr hs
  rw [Nat.card_congr (Equiv.subtypeEquivRight (accum_eq_add_iff s s' γ))]
  by_cases h₂ : (coeffs s).2.1 - (coeffs s').2.1 = 0
  · by_cases h₃ : (coeffs s).2.2 - (coeffs s').2.2 = 0
    · have hpos := natDegree_sub_f1_pos hlen hne hlast (sub_eq_zero.mp h₂) (sub_eq_zero.mp h₃)
      have h₁ : (coeffs s).1 - (coeffs s').1 - C γ ≠ 0 := by
        intro h
        rw [sub_eq_zero.mp h, natDegree_C] at hpos
        exact lt_irrefl 0 hpos
      simp only [h₂, h₃, eval_zero, mul_zero, add_zero]
      calc _ ≤ (s.length - 1) * Nat.card F ^ 2 :=
            card_solutions_le_of_g1 _ γ h₁ (natDegree_sub_f1_le hlen γ)
        _ ≤ s.length * Nat.card F ^ 2 := by gcongr; omega
    · calc _ ≤ (s.length - 1 + 1) * Nat.card F ^ 2 :=
            card_solutions_le_of_g3 _ _ _ γ h₃ (natDegree_sub_f3_le hlen)
        _ = s.length * Nat.card F ^ 2 := by rw [Nat.sub_add_cancel hn]
  · calc _ ≤ (s.length - 1 + 1) * Nat.card F ^ 2 :=
          card_solutions_le_of_g2 _ _ _ γ h₂ (natDegree_sub_f2_le hlen)
      _ = s.length * Nat.card F ^ 2 := by rw [Nat.sub_add_cancel hn]

theorem card_accum_le_of_length_ne {s s' : List (F × F)} (γ : F) (hlen : s.length ≠ s'.length) :
    Nat.card {t : F × F × F // accum t.1 t.2.1 t.2.2 s = accum t.1 t.2.1 t.2.2 s' + γ}
      ≤ (max s.length s'.length + 1) * Nat.card F ^ 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (accum_eq_add_iff s s' γ))]
  rcases Nat.lt_or_gt_of_ne hlen with hlt | hlt
  · obtain ⟨h₂, hd⟩ := sub_f2_of_length_lt hlt
    exact card_solutions_le_of_g2 _ _ _ γ h₂ (hd.trans (le_max_right _ _))
  · obtain ⟨h₂, hd⟩ := sub_f2_of_length_lt hlt
    rw [← neg_sub, natDegree_neg] at hd
    exact card_solutions_le_of_g2 _ _ _ γ (by rwa [← neg_sub, neg_ne_zero])
      (hd.trans (le_max_left _ _))

end PolyXOR.FullProof
