import PolyXORFull

/-!
# Facts about the byte-level model
-/

namespace PolyXOR.FullProof

open Polynomial PolyXOR

/-- Coefficient `i` of `lenPoly n` is bit `i` of `n`, for `i < 64`. -/
theorem coeff_lenPoly (n i : ℕ) :
    (lenPoly n).coeff i = if i < 64 ∧ n.testBit i then 1 else 0 := by
  simp only [lenPoly, finsetSum_coeff, apply_ite (coeff · i), coeff_X_pow, coeff_zero]
  simp [ite_and]
  simp_rw [← Finset.mem_range]
  rw [← Finset.sum_ite_eq _ _ fun x => if n.testBit x then (1 : ZMod 2) else 0]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp_all

theorem lenPoly_injective {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : lenPoly a = lenPoly b) : a = b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < 64
  · have := congrArg (coeff · i) h
    simp only [coeff_lenPoly, hi, true_and] at this
    by_cases h1 : a.testBit i <;> by_cases h2 : b.testBit i <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem degree_lenPoly_lt (n : ℕ) : (lenPoly n).degree < 64 := by
  change _ < ((64 : ℕ) : WithBot ℕ)
  rw [← mem_degreeLT]
  refine Submodule.sum_mem _ fun i hi => ?_
  split_ifs
  · rw [mem_degreeLT, degree_X_pow]
    exact_mod_cast Finset.mem_range.1 hi
  · exact Submodule.zero_mem _

/-- Equal words have equal bytes. -/
theorem byteAt_eq_of_wordAt_eq {m m' : List Byte} {n : ℕ} (h : wordAt m n = wordAt m' n)
    (r : ℕ) (hr : r < 8) : byteAt m (8 * n + r) = byteAt m' (8 * n + r) := by
  have := congrArg (degreeLTEquiv (ZMod 2) 64) h
  simp only [wordAt, LinearEquiv.apply_symm_apply] at this
  funext b
  have hk := congrFun this ⟨8 * r + b, by omega⟩
  simp only at hk
  have e1 : (8 * r + b) / 8 = r := by omega
  have e2 : (⟨(8 * r + ↑b) % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = b := by ext; simp
  rw [e1, e2] at hk
  exact hk

/-- Distinct messages of equal length differ in some word of some block. -/
theorem exists_wordAt_ne {m m' : List Byte} (hlen : m.length = m'.length) (hne : m ≠ m') :
    ∃ β < numBlocks m, ∃ i : Fin 16, wordAt m (16 * β + i) ≠ wordAt m' (16 * β + i) := by
  by_contra hall
  push Not at hall
  apply hne
  refine List.ext_getElem hlen fun j h1 h2 => ?_
  have hw := hall (j / 128) (by unfold numBlocks; omega) ⟨j / 8 % 16, by omega⟩
  have := byteAt_eq_of_wordAt_eq hw (j % 8) (by omega)
  have e : 8 * (16 * (j / 128) + (j / 8 % 16)) + j % 8 = j := by omega
  simp only [e, byteAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

/-- `numChunks m` is the length divided by 4096, rounded up. -/
theorem numChunks_eq (m : List Byte) : numChunks m = (m.length + 4095) / 4096 := by
  unfold numChunks numBlocks
  omega

theorem numChunks_mono {m m' : List Byte} (h : m.length ≤ m'.length) :
    numChunks m ≤ numChunks m' := by
  rw [numChunks_eq, numChunks_eq]
  omega

theorem numChunks_le (m : List Byte) : (numChunks m : ℚ) ≤ m.length / 4096 + 1 := by
  have h : 4096 * numChunks m ≤ m.length + 4096 := by rw [numChunks_eq]; omega
  have h' : (4096 : ℚ) * numChunks m ≤ m.length + 4096 := by exact_mod_cast h
  linarith
