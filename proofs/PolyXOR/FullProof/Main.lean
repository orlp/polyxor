import PolyXOR.FullProof.Poly
import PolyXOR.FullProof.Bytes
import PolyXOR.FullProof.Digest

/-!
# Proof of `polyxor128_axu`

`polyxor128` is the accumulator of `Recurrence` run on `pairs`: one pair
`(h₀, h₁)` per chunk and a final `(0, length)`. Split the key into the block key
and `(z, u, y)`. If the lengths differ, the pair sequences always differ and
`Poly` bounds each fiber. If the lengths are equal, the sequences differ unless
the digests of the chunk containing a differing word collide, which `Digest`
bounds.
-/

namespace PolyXOR.FullProof

open Polynomial PolyXOR

variable {F : Type} [Field F] [Module F4 F]

/-- The pairs fed to the accumulator: one digest per chunk, then `(0, length)`. -/
noncomputable def pairs (ι : (ZMod 2)[X] →+ F) (block : Fin 32 → Fin 16 → Word)
    (m : List Byte) : List (F × F) :=
  (List.range (numChunks m)).map (chunkDigest ι block m) ++ [(0, ι (lenPoly m.length))]

lemma polyxor128_eq (ι : (ZMod 2)[X] →+ F) (block : Fin 32 → Fin 16 → Word) (z u y : F)
    (m : List Byte) : polyxor128 ι (block, z, u, y) m = accum z u y (pairs ι block m) := by
  simp only [polyxor128, accum, pairs, List.foldl_append, List.foldl_map, List.foldl_cons,
    List.foldl_nil, step, add_zero]

lemma length_pairs (ι : (ZMod 2)[X] →+ F) (block : Fin 32 → Fin 16 → Word) (m : List Byte) :
    (pairs ι block m).length = numChunks m + 1 := by
  simp [pairs]

lemma getLast?_pairs (ι : (ZMod 2)[X] →+ F) (block : Fin 32 → Fin 16 → Word) (m : List Byte) :
    (pairs ι block m).getLast? = some (0, ι (lenPoly m.length)) := by
  simp [pairs]

omit [Module F4 F] in
lemma ι_lenPoly_injective {ι : (ZMod 2)[X] →+ F}
    (hι : ∀ x : (ZMod 2)[X], x.degree < 128 → ι x = 0 → x = 0) {a b : ℕ}
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : ι (lenPoly a) = ι (lenPoly b)) : a = b := by
  refine lenPoly_injective ha hb (sub_eq_zero.mp (hι _ ?_ (by rw [map_sub, h, sub_self])))
  refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_) <;>
    exact (degree_lenPoly_lt _).trans (by norm_num)

theorem polyxor128_axu (F : Type) [Field F] [Fintype F] [Module F4 F]
    (hF : Fintype.card F = 2 ^ 128) (ι : (ZMod 2)[X] →+ F)
    (hι : ∀ x : (ZMod 2)[X], x.degree < 128 → ι x = 0 → x = 0)
    (L : ℕ) (m m' : List Byte) (hm : m ≠ m')
    (hL : m.length ≤ L) (hL' : m'.length ≤ L) (h64 : L < 2 ^ 64) (γ : F) :
    (Nat.card {k : Key F // polyxor128 ι k m + polyxor128 ι k m' = γ} : ℚ)
      / Nat.card (Key F) ≤ ((L : ℚ) / 4096 + 3) / 2 ^ 128 := by
  classical
  have hq : Nat.card F = 2 ^ 128 := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_two_of_card hq
  let B := Fin 32 → Fin 16 → Word
  have : Fintype B := Fintype.ofFinite B
  -- The number of `(z, u, y)` realizing `γ` for a fixed block key.
  let fiber : B → ℕ := fun block => Nat.card {t : F × F × F //
    accum t.1 t.2.1 t.2.2 (pairs ι block m) = accum t.1 t.2.1 t.2.2 (pairs ι block m') + γ}
  have hsplit : Nat.card {k : Key F // polyxor128 ι k m + polyxor128 ι k m' = γ}
      = ∑ block : B, fiber block := by
    rw [card_prod_subtype, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun block _ => Nat.card_congr (Equiv.subtypeEquivRight ?_)
    rintro ⟨z, u, y⟩
    rw [polyxor128_eq, polyxor128_eq, ← CharTwo.sub_eq_add, sub_eq_iff_eq_add', add_comm]
  have hkey : (Nat.card (Key F) : ℚ) = Nat.card B * (2 ^ 128) ^ 3 := by
    simp only [Key, Nat.card_prod, hq]
    push_cast
    ring
  have hB : (0 : ℚ) < Nat.card B := by exact_mod_cast Nat.card_pos
  have hk := numChunks_le m
  have hk' := numChunks_le m'
  have hLq : (m.length : ℚ) ≤ L := by exact_mod_cast hL
  have hLq' : (m'.length : ℚ) ≤ L := by exact_mod_cast hL'
  -- It suffices to bound the count by `|B| q² (L/4096 + 3)`.
  suffices hsuff : (Nat.card {k : Key F // polyxor128 ι k m + polyxor128 ι k m' = γ} : ℚ)
      ≤ Nat.card B * (2 ^ 128) ^ 2 * ((L : ℚ) / 4096 + 3) by
    rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
    calc _ ≤ Nat.card B * (2 ^ 128) ^ 2 * ((L : ℚ) / 4096 + 3) * 2 ^ 128 := by gcongr
      _ = _ := by ring
  rw [hsplit]
  push_cast
  by_cases hlen : m.length = m'.length
  · -- Equal lengths: the sequences differ unless the digests of one chunk collide.
    obtain ⟨β, hβ, i, hi⟩ := exists_wordAt_ne hlen hm
    have hnc : numChunks m = numChunks m' := by simp only [numChunks, numBlocks, hlen]
    let E : Finset B := Finset.univ.filter fun block =>
      chunkDigest ι block m (β / 32) = chunkDigest ι block m' (β / 32)
    have hE : (E.card : ℚ) ≤ Nat.card B / 2 ^ 128 := by
      have := card_chunkDigest_eq_le ι hι hlen hβ i hi
      rw [div_le_div_iff₀ hB (by positivity), one_mul] at this
      rw [le_div_iff₀ (by positivity)]
      calc (E.card : ℚ) * 2 ^ 128
          = Nat.card {block : B // chunkDigest ι block m (β / 32)
              = chunkDigest ι block m' (β / 32)} * 2 ^ 128 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ _ := this
    have hβc : β / 32 < numChunks m := by
      simp only [numChunks]
      omega
    have hfib : ∀ block, (fiber block : ℚ)
        ≤ (if block ∈ E then (2 ^ 128 : ℚ) ^ 3 else 0)
          + (numChunks m + 1) * (2 ^ 128) ^ 2 := by
      intro block
      by_cases hmem : block ∈ E
      · simp only [hmem, ite_true]
        have : fiber block ≤ Nat.card (F × F × F) := Finite.card_subtype_le _
        have hc : (Nat.card (F × F × F) : ℚ) = (2 ^ 128) ^ 3 := by
          simp only [Nat.card_prod, hq]; push_cast; ring
        calc (fiber block : ℚ) ≤ Nat.card (F × F × F) := by exact_mod_cast this
          _ = _ := hc
          _ ≤ _ := le_add_of_nonneg_right (by positivity)
      · simp only [hmem, ite_false, zero_add]
        have hne : pairs ι block m ≠ pairs ι block m' := by
          intro h
          apply hmem
          simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
          have h' := congrArg (fun l => l[β / 32]?) h
          simp only [pairs] at h'
          rwa [List.getElem?_append_left (by simpa using hβc),
            List.getElem?_append_left (by simpa [← hnc] using hβc),
            List.getElem?_map, List.getElem?_map, List.getElem?_range hβc,
            List.getElem?_range (hnc ▸ hβc), Option.map_some, Option.map_some,
            Option.some_inj] at h'
        have := card_accum_le_of_length_eq γ (by rw [length_pairs, length_pairs, hnc])
          (by simp [pairs]) hne (by simp [getLast?_pairs])
        rw [length_pairs] at this
        calc (fiber block : ℚ) ≤ ((numChunks m + 1) * Nat.card F ^ 2 : ℕ) := by
              exact_mod_cast this
          _ = _ := by rw [hq]; push_cast; ring
    calc ∑ block : B, (fiber block : ℚ)
        ≤ ∑ block : B, ((if block ∈ E then (2 ^ 128 : ℚ) ^ 3 else 0)
            + (numChunks m + 1) * (2 ^ 128) ^ 2) := Finset.sum_le_sum fun b _ => hfib b
      _ = E.card * (2 ^ 128) ^ 3 + Nat.card B * ((numChunks m + 1) * (2 ^ 128) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ,
          ← Nat.card_eq_fintype_card]
      _ ≤ Nat.card B / 2 ^ 128 * (2 ^ 128) ^ 3
            + Nat.card B * ((numChunks m + 1) * (2 ^ 128) ^ 2) := by gcongr
      _ = Nat.card B * (2 ^ 128) ^ 2 * (numChunks m + 2) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · -- Different lengths: the final pairs differ, so the sequences always differ.
    have hne : ∀ block, pairs ι block m ≠ pairs ι block m' := by
      intro block h
      have h' := congrArg List.getLast? h
      rw [getLast?_pairs, getLast?_pairs, Option.some_inj, Prod.mk.injEq] at h'
      exact hlen (ι_lenPoly_injective hι (hL.trans_lt h64) (hL'.trans_lt h64) h'.2)
    by_cases hnc : numChunks m = numChunks m'
    · have hfib : ∀ block, (fiber block : ℚ) ≤ (numChunks m + 1) * (2 ^ 128) ^ 2 := by
        intro block
        have := card_accum_le_of_length_eq γ (by rw [length_pairs, length_pairs, hnc])
          (by simp [pairs]) (hne block) (by simp [getLast?_pairs])
        rw [length_pairs] at this
        calc (fiber block : ℚ) ≤ ((numChunks m + 1) * Nat.card F ^ 2 : ℕ) := by
              exact_mod_cast this
          _ = _ := by rw [hq]; push_cast; ring
      calc ∑ block : B, (fiber block : ℚ)
          ≤ ∑ _block : B, ((numChunks m + 1 : ℚ) * (2 ^ 128) ^ 2) :=
            Finset.sum_le_sum fun b _ => hfib b
        _ = Nat.card B * (2 ^ 128) ^ 2 * (numChunks m + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have hfib : ∀ block, (fiber block : ℚ)
          ≤ (max (numChunks m) (numChunks m') + 2) * (2 ^ 128) ^ 2 := by
        intro block
        have := card_accum_le_of_length_ne (s := pairs ι block m) (s' := pairs ι block m') γ
          (by rw [length_pairs, length_pairs]; omega)
        rw [length_pairs, length_pairs, max_add_add_right] at this
        calc (fiber block : ℚ)
            ≤ ((max (numChunks m) (numChunks m') + 1 + 1) * Nat.card F ^ 2 : ℕ) := by
              exact_mod_cast this
          _ = _ := by rw [hq]; push_cast; ring
      have hmax : ((max (numChunks m) (numChunks m') : ℕ) : ℚ) ≤ L / 4096 + 1 := by
        rw [Nat.cast_max]
        exact max_le (by linarith) (by linarith)
      calc ∑ block : B, (fiber block : ℚ)
          ≤ ∑ _block : B, ((max (numChunks m) (numChunks m') + 2 : ℚ) * (2 ^ 128) ^ 2) :=
            Finset.sum_le_sum fun b _ => by exact_mod_cast hfib b
        _ = Nat.card B * (2 ^ 128) ^ 2 * (max (numChunks m) (numChunks m') + 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end PolyXOR.FullProof
