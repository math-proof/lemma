import Mathlib
import sympy.Basic
import sympy.series.formal.IntegerCompositions
open Finset
open scoped BigOperators


/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_ge_len_le
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.len α
    ≤ AlgebraicCombinatorics.Composition.size α := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_ge_len α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_singleton_eq
-- given
  (n : PNat) :
-- imply
  AlgebraicCombinatorics.Composition.size
    (AlgebraicCombinatorics.Composition.singleton n) = n.val := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_singleton n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_len_singleton_eq
-- given
  (n : PNat) :
-- imply
  AlgebraicCombinatorics.Composition.len
    (AlgebraicCombinatorics.Composition.singleton n) = 1 := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_singleton n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_append_eq
-- given
  (α β : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.size (α ++ β) =
    AlgebraicCombinatorics.Composition.size α +
      AlgebraicCombinatorics.Composition.size β := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_append α β

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_len_append_eq
-- given
  (α β : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.len (α ++ β) =
    AlgebraicCombinatorics.Composition.len α +
      AlgebraicCombinatorics.Composition.len β := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_append α β

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_to_blocks_of_blocks_eq
-- given
  (blocks : List ℕ) (hpos : ∀ {i}, i ∈ blocks → 0 < i) :
-- imply
  AlgebraicCombinatorics.Composition.toBlocks
    (AlgebraicCombinatorics.Composition.ofBlocks blocks hpos) = blocks := by
-- proof
  apply AlgebraicCombinatorics.Composition.toBlocks_ofBlocks blocks hpos

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_of_blocks_to_blocks_eq
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.ofBlocks
    (AlgebraicCombinatorics.Composition.toBlocks α)
    (fun hi => by
      simp only [AlgebraicCombinatorics.Composition.toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2) = α := by
-- proof
  apply AlgebraicCombinatorics.Composition.ofBlocks_toBlocks α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_size_eq_sum_to_blocks_eq
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.size α =
    (AlgebraicCombinatorics.Composition.toBlocks α).sum := by
-- proof
  apply AlgebraicCombinatorics.Composition.size_eq_sum_toBlocks α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_len_eq_to_blocks_length_eq
-- given
  (α : AlgebraicCombinatorics.Composition) :
-- imply
  AlgebraicCombinatorics.Composition.len α =
    (AlgebraicCombinatorics.Composition.toBlocks α).length := by
-- proof
  apply AlgebraicCombinatorics.Composition.len_eq_toBlocks_length α

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_into_parts_pos_eq
-- given
  (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSizeIntoParts n k) =
    Nat.choose (n - 1) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSizeIntoParts_pos n k hn hk

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_into_parts_k_zero_eq
-- given
  (n : ℕ) (hn : 0 < n) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSizeIntoParts n 0) = 0 := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSizeIntoParts_k_zero n hn

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_into_parts_zero_eq
-- given
  (k : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSizeIntoParts 0 k) =
    if k = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSizeIntoParts_zero k

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_eq
-- given
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSize n) =
    if n = 0 then 1 else 2 ^ (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSize n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma composition_card_of_size_pos_eq
-- given
  (n : ℕ) (hn : 0 < n) :
-- imply
  Fintype.card (AlgebraicCombinatorics.Composition.ofSize n) = 2 ^ (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.Composition.card_ofSize_pos n hn

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma mathlib_composition_card_compositions_of_length_eq
-- given
  (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
-- imply
  ((Finset.univ : Finset (_root_.Composition n)).filter
    (fun c => c.length = k)).card = Nat.choose (n - 1) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.MathlibComposition.card_compositions_of_length n k hn hk

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_card_of_size_into_parts_eq
-- given
  (n k : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts n k) =
    Nat.choose (n + k - 1) n := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.card_ofSizeIntoParts n k

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_card_of_size_into_parts_pos_eq
-- given
  (n k : ℕ) (hk : 0 < k) :
-- imply
  Fintype.card (AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts n k) =
    Nat.choose (n + k - 1) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.card_ofSizeIntoParts_pos n k hk

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_card_of_size_into_parts_zero_eq
-- given
  (n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts n 0) =
    if n = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.card_ofSizeIntoParts_zero n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma weak_composition_of_size_into_parts_ext_eq
-- given
  {n k : ℕ} {x y : AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts' n k}
  (h : x.val = y.val) :
-- imply
  x = y := by
-- proof
  apply AlgebraicCombinatorics.WeakComposition.ofSizeIntoParts'.ext h

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma bounded_weak_composition_card_eq
-- given
  (n k p : ℕ) :
-- imply
  (Fintype.card (AlgebraicCombinatorics.BoundedWeakComposition n k p) : ℤ) =
    ∑ j ∈ (range (k + 1)).filter (fun j => p * j ≤ n),
      (-1 : ℤ) ^ j * (Nat.choose k j) *
        (Nat.choose (n - p * j + k - 1) (n - p * j)) := by
-- proof
  apply AlgebraicCombinatorics.BoundedWeakComposition.card n k p

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma card_bounded_weak_composition_2_eq
-- given
  (k n : ℕ) :
-- imply
  Fintype.card (AlgebraicCombinatorics.BoundedWeakComposition n k 2) =
    Nat.choose k n := by
-- proof
  apply AlgebraicCombinatorics.card_boundedWeakComposition_2 k n

/-- [IntegerCompositions](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/IntegerCompositions.lean) -/
@[path]
private lemma binom_sum_identity_eq
-- given
  (n k : ℕ) :
-- imply
  (Nat.choose k n : ℤ) =
    ∑ j ∈ (range (k + 1)).filter (fun j => 2 * j ≤ n),
      (-1 : ℤ) ^ j * (Nat.choose k j) *
        (Nat.choose (n - 2 * j + k - 1) (n - 2 * j)) := by
-- proof
  apply AlgebraicCombinatorics.binom_sum_identity n k


-- created on 2026-10-11
