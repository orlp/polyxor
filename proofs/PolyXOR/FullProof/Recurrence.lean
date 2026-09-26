import Mathlib

/-!
# The injective recurrence

The accumulator `acc ← (acc + u)(b + y) + a`, started at `z`, as a polynomial:
`accum z u y s = f₁(y) + z f₂(y) + u f₃(y)` with `(f₁, f₂, f₃) = coeffs s`.
-/

namespace PolyXOR.FullProof

open Polynomial

variable {F : Type*} [Field F]

/-- One step of the accumulator on the pair `p = (a, b)`. -/
def step (u y acc : F) (p : F × F) : F := (acc + u) * (p.2 + y) + p.1

/-- The accumulator after the pairs `s`, starting from `z`. -/
def accum (z u y : F) (s : List (F × F)) : F := s.foldl (step u y) z

/-- The coefficient polynomials `(f₁, f₂, f₃)` in `y`. -/
noncomputable def coeffs (s : List (F × F)) : F[X] × F[X] × F[X] :=
  s.foldl (fun f p => (C p.1 + (C p.2 + X) * f.1, (C p.2 + X) * f.2.1, (C p.2 + X) * (f.2.2 + 1)))
    (0, 1, 0)

/-- The step function of `coeffs`. -/
noncomputable def coeffStep (f : F[X] × F[X] × F[X]) (p : F × F) : F[X] × F[X] × F[X] :=
  (C p.1 + (C p.2 + X) * f.1, (C p.2 + X) * f.2.1, (C p.2 + X) * (f.2.2 + 1))

theorem coeffs_eq_foldl (s : List (F × F)) : coeffs s = s.foldl coeffStep (0, 1, 0) := rfl

@[simp] theorem coeffs_nil : coeffs ([] : List (F × F)) = (0, 1, 0) := rfl

/-- The fold of `coeffs` from an arbitrary start is affine in the start. -/
theorem foldl_coeffStep (s : List (F × F)) (x y z : F[X]) :
    s.foldl coeffStep (x, y, z) =
      (x * (coeffs s).2.1 + (coeffs s).1, y * (coeffs s).2.1,
        z * (coeffs s).2.1 + (coeffs s).2.2) := by
  induction s generalizing x y z with
  | nil => simp
  | cons p t ih =>
    rw [coeffs_eq_foldl, List.foldl_cons, List.foldl_cons, coeffStep, coeffStep]
    dsimp only
    rw [ih, ih]
    simp only [Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

/-- The front recurrence for `coeffs`. -/
theorem coeffs_cons (p : F × F) (t : List (F × F)) :
    coeffs (p :: t) = (C p.1 * (coeffs t).2.1 + (coeffs t).1, (C p.2 + X) * (coeffs t).2.1,
      (C p.2 + X) * (coeffs t).2.1 + (coeffs t).2.2) := by
  rw [coeffs_eq_foldl, List.foldl_cons, coeffStep, foldl_coeffStep]
  simp

theorem f3_cons (p : F × F) (t : List (F × F)) :
    (coeffs (p :: t)).2.2 = (coeffs (p :: t)).2.1 + (coeffs t).2.2 := by
  simp [coeffs_cons]

theorem monic_C_add_X (b : F) : (C b + X : F[X]).Monic := by
  rw [add_comm]; exact monic_X_add_C b

/-- `f₂` is monic of degree the length. -/
theorem f2_monic (s : List (F × F)) :
    (coeffs s).2.1.Monic ∧ (coeffs s).2.1.natDegree = s.length := by
  induction s with
  | nil => simp
  | cons p t ih =>
    have hd : (C p.2 + X : F[X]).natDegree = 1 := by rw [add_comm]; exact natDegree_X_add_C _
    simp only [coeffs_cons, List.length_cons]
    refine ⟨(monic_C_add_X _).mul ih.1, ?_⟩
    rw [(monic_C_add_X _).natDegree_mul ih.1, hd, ih.2, add_comm]

/-- `f₃ + 1` is monic of degree the length. -/
theorem f3_add_one_monic (s : List (F × F)) :
    ((coeffs s).2.2 + 1).Monic ∧ ((coeffs s).2.2 + 1).natDegree = s.length := by
  induction s with
  | nil => simp
  | cons p t ih =>
    obtain ⟨hm, hd⟩ := f2_monic (p :: t)
    rw [f3_cons, add_assoc]
    have hlt : ((coeffs t).2.2 + 1).degree < (coeffs (p :: t)).2.1.degree := by
      rw [degree_eq_natDegree ih.1.ne_zero, degree_eq_natDegree hm.ne_zero, ih.2, hd]
      exact_mod_cast Nat.lt_succ_self _
    exact ⟨hm.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hd]⟩

/-- `f₁` has degree less than the length. -/
theorem f1_natDegree_le (s : List (F × F)) : (coeffs s).1.natDegree ≤ s.length - 1 := by
  induction s with
  | nil => simp
  | cons p t ih =>
    simp only [coeffs_cons, List.length_cons]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · have h1 := natDegree_C_mul_le p.1 (coeffs t).2.1
      have h2 := (f2_monic t).2
      omega
    · omega

theorem natDegree_sub_le_of_monic {p q : F[X]} {n : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpn : p.natDegree = n) (hqn : q.natDegree = n) : (p - q).natDegree ≤ n - 1 := by
  apply natDegree_le_pred
  · exact (natDegree_sub_le _ _).trans (by omega)
  · rw [coeff_sub, ← hpn, hp.coeff_natDegree, hpn, ← hqn, hq.coeff_natDegree, sub_self]

theorem coeff_C_add_X_mul (b : F) (f : F[X]) (n : ℕ) :
    ((C b + X) * f).coeff (n + 1) = b * f.coeff (n + 1) + f.coeff n := by
  rw [add_mul, coeff_add, coeff_C_mul, coeff_X_mul]

/-- Equal `f₂`, `f₃` on `p :: t`, `p' :: t'` force equal `b` and equal `f₂`, `f₃` on the
tails. -/
theorem cons_eq_of_f2_f3 {p p' : F × F} {t t' : List (F × F)} (hlen : t.length = t'.length)
    (h2 : (coeffs (p :: t)).2.1 = (coeffs (p' :: t')).2.1)
    (h3 : (coeffs (p :: t)).2.2 = (coeffs (p' :: t')).2.2) :
    p.2 = p'.2 ∧ (coeffs t).2.1 = (coeffs t').2.1 ∧ (coeffs t).2.2 = (coeffs t').2.2 := by
  have h3t : (coeffs t).2.2 = (coeffs t').2.2 := by
    rw [f3_cons, f3_cons, h2] at h3; exact add_left_cancel h3
  simp only [coeffs_cons] at h2
  have hb : p.2 = p'.2 := by
    cases t with
    | nil =>
      cases t' with
      | nil => simpa using congrArg (fun f => f.coeff 0) h2
      | cons _ _ => simp at hlen
    | cons q r =>
      cases t' with
      | nil => simp at hlen
      | cons q' r' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        have hQ : (coeffs r).2.2.coeff r.length = (coeffs r').2.2.coeff r.length := by
          have a := (f3_add_one_monic r).1.coeff_natDegree
          have b := (f3_add_one_monic r').1.coeff_natDegree
          rw [(f3_add_one_monic r).2, coeff_add] at a
          rw [(f3_add_one_monic r').2, ← hlen, coeff_add] at b
          linear_combination a - b
        have hc : (coeffs (q :: r)).2.1.coeff r.length
            = (coeffs (q' :: r')).2.1.coeff r.length := by
          have e := congrArg (fun f => f.coeff r.length) h3t
          simp only [f3_cons, coeff_add] at e
          linear_combination e - hQ
        have e := congrArg (fun f => f.coeff (r.length + 1)) h2
        simp only [coeff_C_add_X_mul] at e
        have m := (f2_monic (q :: r)).1.coeff_natDegree
        have m' := (f2_monic (q' :: r')).1.coeff_natDegree
        rw [(f2_monic (q :: r)).2, List.length_cons] at m
        rw [(f2_monic (q' :: r')).2, List.length_cons, ← hlen] at m'
        rw [m, m'] at e
        linear_combination e - hc
  rw [hb] at h2
  exact ⟨hb, mul_left_cancel₀ (monic_C_add_X _).ne_zero h2, h3t⟩

theorem accum_eq (z u y : F) (s : List (F × F)) :
    accum z u y s = (coeffs s).1.eval y + z * (coeffs s).2.1.eval y
      + u * (coeffs s).2.2.eval y := by
  induction s generalizing z with
  | nil => simp [accum]
  | cons p t ih =>
    simp only [accum, List.foldl_cons] at ih ⊢
    rw [ih, coeffs_cons, step]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    ring

/-- For equal lengths, `f₁ - f₁' - γ` has degree `< n`. -/
theorem natDegree_sub_f1_le {s s' : List (F × F)} (hlen : s.length = s'.length) (γ : F) :
    ((coeffs s).1 - (coeffs s').1 - C γ).natDegree ≤ s.length - 1 := by
  have h1 := f1_natDegree_le s
  have h2 := f1_natDegree_le s'
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  · exact h1
  · omega
  · simp

/-- For equal lengths, `f₂ - f₂'` has degree `< n`: the leading `yⁿ` cancels. -/
theorem natDegree_sub_f2_le {s s' : List (F × F)} (hlen : s.length = s'.length) :
    ((coeffs s).2.1 - (coeffs s').2.1).natDegree ≤ s.length - 1 := by
  obtain ⟨hm, hd⟩ := f2_monic s
  obtain ⟨hm', hd'⟩ := f2_monic s'
  exact natDegree_sub_le_of_monic hm hm' hd (hd'.trans hlen.symm)

/-- For equal lengths, `f₃ - f₃'` has degree `< n`: the leading `yⁿ` cancels. -/
theorem natDegree_sub_f3_le {s s' : List (F × F)} (hlen : s.length = s'.length) :
    ((coeffs s).2.2 - (coeffs s').2.2).natDegree ≤ s.length - 1 := by
  obtain ⟨hm, hd⟩ := f3_add_one_monic s
  obtain ⟨hm', hd'⟩ := f3_add_one_monic s'
  rw [show (coeffs s).2.2 - (coeffs s').2.2
      = ((coeffs s).2.2 + 1) - ((coeffs s').2.2 + 1) by ring]
  exact natDegree_sub_le_of_monic hm hm' hd (hd'.trans hlen.symm)

/-- For different lengths, `f₂ - f₂'` is nonzero of degree at most the larger length. -/
theorem sub_f2_of_length_lt {s s' : List (F × F)} (hlt : s.length < s'.length) :
    (coeffs s).2.1 - (coeffs s').2.1 ≠ 0 ∧
      ((coeffs s).2.1 - (coeffs s').2.1).natDegree ≤ s'.length := by
  have hd := (f2_monic s).2
  have hd' := (f2_monic s').2
  have hsub := natDegree_sub_eq_right_of_natDegree_lt (p := (coeffs s).2.1)
    (q := (coeffs s').2.1) (by omega)
  refine ⟨fun h0 => ?_, by omega⟩
  rw [h0, natDegree_zero] at hsub
  omega

/-- Injectivity: distinct sequences of equal length with equal last `a` and equal
`f₂`, `f₃` have `f₁ - f₁'` nonconstant. -/
theorem natDegree_sub_f1_pos {s s' : List (F × F)} (hlen : s.length = s'.length) (hne : s ≠ s')
    (hlast : (s.getLast?).map Prod.fst = (s'.getLast?).map Prod.fst)
    (h2 : (coeffs s).2.1 = (coeffs s').2.1) (h3 : (coeffs s).2.2 = (coeffs s').2.2) :
    0 < ((coeffs s).1 - (coeffs s').1).natDegree := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hlen
  | cons p t ih =>
    cases s' with
    | nil => simp at hlen
    | cons p' t' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨hb, h2t, h3t⟩ := cons_eq_of_f2_f3 hlen h2 h3
      simp only [coeffs_cons]
      rw [show C p.1 * (coeffs t).2.1 + (coeffs t).1 - (C p'.1 * (coeffs t').2.1 + (coeffs t').1)
          = C (p.1 - p'.1) * (coeffs t).2.1 + ((coeffs t).1 - (coeffs t').1) by
        rw [h2t, C_sub]; ring]
      have ht : t ≠ [] := by
        rintro rfl
        obtain rfl : t' = [] := List.eq_nil_of_length_eq_zero hlen.symm
        simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at hlast
        exact hne (by rw [Prod.ext hlast hb])
      have ht' : t' ≠ [] := by rintro rfl; exact ht (List.eq_nil_of_length_eq_zero hlen)
      have hlast' : t.getLast?.map Prod.fst = t'.getLast?.map Prod.fst := by
        obtain ⟨q, r, rfl⟩ := List.exists_cons_of_ne_nil ht
        obtain ⟨q', r', rfl⟩ := List.exists_cons_of_ne_nil ht'
        simpa using hlast
      by_cases ha : p.1 = p'.1
      · have htt : t ≠ t' := by rintro rfl; exact hne (by rw [Prod.ext ha hb])
        simpa [ha] using ih hlen htt hlast' h2t h3t
      · have hpos : 0 < t.length := List.length_pos_iff.2 ht
        have hlead : (C (p.1 - p'.1) * (coeffs t).2.1).natDegree = t.length := by
          rw [natDegree_C_mul (sub_ne_zero.2 ha), (f2_monic t).2]
        have hrest : ((coeffs t).1 - (coeffs t').1).natDegree ≤ t.length - 1 :=
          (natDegree_sub_le _ _).trans
            (max_le (f1_natDegree_le t) (hlen ▸ f1_natDegree_le t'))
        rw [natDegree_add_eq_left_of_natDegree_lt (by omega), hlead]
        exact hpos

end PolyXOR.FullProof
