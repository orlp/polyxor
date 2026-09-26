import PolyXORFull
import PolyXOR.CompressProof.Main

/-!
# Chunk digests collide with probability at most `2⁻¹²⁸`

Follows from `compress_axu128_is_axu` for the compression call whose input
contains the differing word.
-/

namespace PolyXOR.FullProof

open Polynomial PolyXOR

/-! ### The two compression calls of `hashBlock` -/

/-- `slot j t` is such that word `2 * slot j t + p` of a block is word `t` of argument `j` of
the compression call of parity `p`. -/
def slot : Fin 4 → Fin 2 → Fin 8 := ![![0, 6], ![1, 7], ![4, 2], ![5, 3]]

/-- The word index of word `t` of argument `j` of the compression call of parity `p`. -/
def idx (p : Fin 2) (j : Fin 4) (t : Fin 2) : Fin 16 :=
  ⟨2 * (slot j t).val + p.val, by have := (slot j t).isLt; have := p.isLt; omega⟩

/-- The input of the compression call of parity `p`. -/
def sel (p : Fin 2) (w : Fin 16 → Word) : Block := fun j => (w (idx p j 0), w (idx p j 1))

lemma sel_add (p : Fin 2) (u v : Fin 16 → Word) : sel p (u + v) = sel p u + sel p v := rfl

/-- Places a `Block` at the words of the compression call of parity `p`. -/
noncomputable def place (p : Fin 2) (k : Block) (i : Fin 16) : Word :=
  if i.val % 2 = p.val then
    ![(k 0).1, (k 1).1, (k 2).2, (k 3).2, (k 2).1, (k 3).1, (k 0).2, (k 1).2]
      ⟨i.val / 2, by omega⟩
  else 0

lemma sel_place (p : Fin 2) (k : Block) : sel p (place p k) = k := by
  funext j
  fin_cases p <;> fin_cases j <;> simp [sel, place, idx, slot]

lemma sel_place_other (p : Fin 2) (k : Block) : sel (p + 1) (place p k) = 0 := by
  funext j
  fin_cases p <;> fin_cases j <;> simp [sel, place, idx, slot]

lemma sel_congr {p : Fin 2} {w w' : Fin 16 → Word} (h : sel p w = sel p w') (j : Fin 4)
    (t : Fin 2) : w (idx p j t) = w' (idx p j t) := by
  fin_cases t
  · exact congrArg Prod.fst (congrFun h j)
  · exact congrArg Prod.snd (congrFun h j)

lemma exists_idx (i : Fin 16) : ∃ p j t, idx p j t = i := by
  revert i; decide

/-! ### Counting -/

/-- If every translate `g + e k` satisfies `P` for at most a `2⁻¹²⁸` fraction of `k`, then so
does a uniformly random `g`. -/
lemma card_le_of_translates {G K : Type} [AddGroup G] [Finite G] [Finite K] [Nonempty G]
    [Nonempty K] (P : G → Prop) (e : K → G)
    (h : ∀ g, (Nat.card {k : K // P (g + e k)} : ℚ) / Nat.card K ≤ 1 / 2 ^ 128) :
    (Nat.card {g : G // P g} : ℚ) / Nat.card G ≤ 1 / 2 ^ 128 := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite K
  have hK : (0 : ℚ) < Nat.card K := by exact_mod_cast Nat.card_pos
  have hG : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hc : ∀ g, (Nat.card {k : K // P (g + e k)} : ℚ) = ∑ k, if P (g + e k) then 1 else 0 := by
    intro g
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hN : ∀ k, (Nat.card {g : G // P g} : ℚ) = ∑ g, if P (g + e k) then 1 else 0 := by
    intro k
    rw [Fintype.sum_equiv (Equiv.addRight (e k)) (fun g => if P (g + e k) then (1 : ℚ) else 0)
      (fun g => if P g then (1 : ℚ) else 0) (fun _ => rfl)]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum : ∑ g, (Nat.card {k : K // P (g + e k)} : ℚ)
      = Nat.card K * Nat.card {g : G // P g} := by
    simp_rw [hc]
    rw [Finset.sum_comm]
    simp_rw [← hN]
    simp [Nat.card_eq_fintype_card]
  have hle : ∑ g, (Nat.card {k : K // P (g + e k)} : ℚ)
      ≤ Nat.card G * (Nat.card K / 2 ^ 128) := by
    calc ∑ g, (Nat.card {k : K // P (g + e k)} : ℚ)
        ≤ ∑ _g : G, (Nat.card K / 2 ^ 128 : ℚ) := by
          gcongr with g
          have := h g
          rw [div_le_iff₀ hK] at this
          linarith
      _ = Nat.card G * (Nat.card K / 2 ^ 128) := by simp [Nat.card_eq_fintype_card]
  rw [hsum] at hle
  rw [div_le_iff₀ hG]
  have : (Nat.card K : ℚ) * Nat.card {g : G // P g} ≤ Nat.card K * (1 / 2 ^ 128 * Nat.card G) := by
    linarith
  exact le_of_mul_le_mul_left this hK

/-- In an additive group of exponent two, moving terms across `=` keeps their sign. -/
lemma add_eq_add_iff_of_char_two {M : Type} [AddCommGroup M] (hM : ∀ x : M, -x = x)
    (a a' y y' : M) : a + y = a' + y' ↔ a + a' = y + y' := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := a + a'), sub_eq_add_neg, sub_eq_add_neg, hM, hM,
    show a + y + (a' + y') = a + a' + (y + y') by abel]

/-! ### Chunk digests -/

variable {F : Type} [Field F] [Module F4 F]

/-- `hashBlock` is the sum of the compression calls of both parities. -/
lemma hashBlock_eq (ι : (ZMod 2)[X] →+ F) (p : Fin 2) (w : Fin 16 → Word) :
    hashBlock ι w = compress ι (sel p w) + compress ι (sel (p + 1) w) := by
  fin_cases p
  · rfl
  · exact add_comm _ _

theorem card_chunkDigest_eq_le (ι : (ZMod 2)[X] →+ F)
    (hι : ∀ x : (ZMod 2)[X], x.degree < 128 → ι x = 0 → x = 0)
    {m m' : List Byte} (hlen : m.length = m'.length) {β : ℕ} (hβ : β < numBlocks m) (i : Fin 16)
    (hi : wordAt m (16 * β + i) ≠ wordAt m' (16 * β + i)) :
    (Nat.card {block : Fin 32 → Fin 16 → Word //
        chunkDigest ι block m (β / 32) = chunkDigest ι block m' (β / 32)} : ℚ)
      / Nat.card (Fin 32 → Fin 16 → Word) ≤ 1 / 2 ^ 128 := by
  generalize hc : β / 32 = c
  set b₀ : Fin 32 := ⟨β % 32, Nat.mod_lt _ (by norm_num)⟩
  have hb : 32 * c + (b₀ : ℕ) = β := by rw [← hc]; exact Nat.div_add_mod β 32
  have hnum : numBlocks m' = numBlocks m := by simp only [numBlocks, hlen]
  set S := Finset.univ.filter (fun b : Fin 32 => 32 * c + b < numBlocks m)
  have hb₀ : b₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb ▸ hβ⟩
  obtain ⟨p, j, t, hidx⟩ := exists_idx i
  have hM : ∀ x : F × F, -x = x := CompressProof.neg_self F4
  let e : Block → Fin 32 → Fin 16 → Word := fun k => Pi.single b₀ (place p k)
  refine card_le_of_translates _ e fun g => ?_
  have hdec : ∀ (n : List Byte) (k : Block), numBlocks n = numBlocks m →
      chunkDigest ι (g + e k) n c
        = compress ι (sel p ((fun i : Fin 16 => wordAt n (16 * (32 * c + b₀) + i)) + g b₀) + k)
          + (compress ι (sel (p + 1) ((fun i : Fin 16 => wordAt n (16 * (32 * c + b₀) + i)) + g b₀))
            + ∑ b ∈ S.erase b₀, hashBlock ι fun i => wordAt n (16 * (32 * c + b) + i) + g b i) := by
    intro n k hn
    simp only [chunkDigest, hn]
    rw [← Finset.add_sum_erase S _ hb₀, ← add_assoc]
    refine congrArg₂ (· + ·) ?_ ?_
    · have hw : (fun i : Fin 16 => wordAt n (16 * (32 * c + b₀) + i) + (g + e k) b₀ i)
          = (fun i : Fin 16 => wordAt n (16 * (32 * c + b₀) + i)) + (g b₀ + place p k) := by
        funext i
        simp [e]
      rw [hw, hashBlock_eq ι p, ← add_assoc, sel_add p _ (place p k), sel_add (p + 1) _ (place p k),
        sel_place, sel_place_other, add_zero]
    · refine Finset.sum_congr rfl fun b hb => ?_
      have : e k b = 0 := Pi.single_eq_of_ne (Finset.ne_of_mem_erase hb) _
      simp only [Pi.add_apply, this, Pi.zero_apply, add_zero]
  have hne : sel p ((fun i : Fin 16 => wordAt m (16 * (32 * c + b₀) + i)) + g b₀)
      ≠ sel p ((fun i : Fin 16 => wordAt m' (16 * (32 * c + b₀) + i)) + g b₀) := by
    intro h
    have h2 := add_right_cancel (sel_congr h j t)
    rw [hb, hidx] at h2
    exact hi h2
  have hbound := CompressProof.compress_axu128_is_axu F ι hι _ _ hne
    ((compress ι (sel (p + 1) ((fun i : Fin 16 => wordAt m (16 * (32 * c + b₀) + i)) + g b₀))
      + ∑ b ∈ S.erase b₀, hashBlock ι fun i => wordAt m (16 * (32 * c + b) + i) + g b i)
    + (compress ι (sel (p + 1) ((fun i : Fin 16 => wordAt m' (16 * (32 * c + b₀) + i)) + g b₀))
      + ∑ b ∈ S.erase b₀, hashBlock ι fun i => wordAt m' (16 * (32 * c + b) + i) + g b i))
  rwa [← Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun k => chunkDigest ι (g + e k) m c = chunkDigest ι (g + e k) m' c) fun k => by
    rw [hdec m k rfl, hdec m' k hnum]; exact add_eq_add_iff_of_char_two hM _ _ _ _)] at hbound

end PolyXOR.FullProof
