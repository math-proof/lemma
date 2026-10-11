import Mathlib
import sympy.Basic
import sympy.combinatorics.partitions.Basics
open Finset
open IversonBracket
open Nat.Partition
open PowerSeries
open BigOperators
open scoped PowerSeries.WithPiTopology


/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_true_eq_one
  {α} [Zero α] [One α]
  {P : Prop} [Decidable P]
-- given
  (h : P) :
-- imply
  (⦃P⦄ : α) = 1 := by
-- proof
  apply IversonBracket.iverson_true h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_false_eq_zero
  {α} [Zero α] [One α]
  {P : Prop} [Decidable P]
-- given
  (h : ¬P) :
-- imply
  (⦃P⦄ : α) = 0 := by
-- proof
  apply IversonBracket.iverson_false h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_eq_one_iff
  {α} [Zero α] [One α] [NeZero (1 : α)]
  {P : Prop} [Decidable P] :
-- imply
  (⦃P⦄ : α) = 1 ↔ P := by
-- proof
  apply IversonBracket.iverson_eq_one_iff

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_eq_zero_iff
  {α} [Zero α] [One α] [NeZero (1 : α)]
  {P : Prop} [Decidable P] :
-- imply
  (⦃P⦄ : α) = 0 ↔ ¬P := by
-- proof
  apply IversonBracket.iverson_eq_zero_iff

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma kronecker_eq_iverson
  {α : Type u} [DecidableEq α]
  {R} [Zero R] [One R]
-- given
  (i j : α) :
-- imply
  (if i = j then (1 : R) else 0) = ⦃i = j⦄ := by
-- proof
  apply IversonBracket.kronecker_eq_iverson i j

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_nat_eq_toNat
-- given
  (P : Prop) [Decidable P] :
-- imply
  (⦃P⦄ : ℕ) = (decide P).toNat := by
-- proof
  apply IversonBracket.iverson_nat_eq_toNat P

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma sum_iverson_eq_card
  {α}
-- given
  (s : Finset α)
  (p : α → Prop) [DecidablePred p] :
-- imply
  ∑ x ∈ s, (⦃p x⦄ : ℕ) = (s.filter p).card := by
-- proof
  apply IversonBracket.sum_iverson_eq_card s p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_and_eq
  {α} [MulZeroOneClass α]
  {P Q : Prop} [Decidable P] [Decidable Q] :
-- imply
  (⦃P ∧ Q⦄ : α) = ⦃P⦄ * ⦃Q⦄ := by
-- proof
  apply IversonBracket.iverson_and

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_sq_eq
  {α} [MonoidWithZero α]
  {P : Prop} [Decidable P] :
-- imply
  (⦃P⦄ : α) ^ 2 = ⦃P⦄ := by
-- proof
  apply IversonBracket.iverson_sq

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_not_eq
  {α} [Ring α] [NeZero (1 : α)]
  {P : Prop} [Decidable P] :
-- imply
  (⦃¬P⦄ : α) = 1 - ⦃P⦄ := by
-- proof
  apply IversonBracket.iverson_not

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_or_eq
  {α} [Ring α]
  {P Q : Prop} [Decidable P] [Decidable Q] :
-- imply
  (⦃P ∨ Q⦄ : α) = ⦃P⦄ + ⦃Q⦄ - ⦃P⦄ * ⦃Q⦄ := by
-- proof
  apply IversonBracket.iverson_or

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_imp_eq
  {α} [Ring α]
  {P Q : Prop} [Decidable P] [Decidable Q] :
-- imply
  (⦃P → Q⦄ : α) = 1 - ⦃P⦄ * (1 - ⦃Q⦄) := by
-- proof
  apply IversonBracket.iverson_imp

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_def_iff
-- given
  (a : ℝ)
  (n : ℤ) :
-- imply
  n ≤ ⌊a⌋ ↔ n ≤ a := by
-- proof
  apply FloorCeiling.floor_def a n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_def_iff
-- given
  (a : ℝ)
  (n : ℤ) :
-- imply
  ⌈a⌉ ≤ n ↔ a ≤ n := by
-- proof
  apply FloorCeiling.ceil_def a n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_le
-- given
  (a : ℝ) :
-- imply
  (⌊a⌋ : ℝ) ≤ a := by
-- proof
  apply FloorCeiling.floor_le a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma le_ceil
-- given
  (a : ℝ) :
-- imply
  a ≤ ⌈a⌉ := by
-- proof
  apply FloorCeiling.le_ceil a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_le_ceil
-- given
  (a : ℝ) :
-- imply
  ⌊a⌋ ≤ ⌈a⌉ := by
-- proof
  apply FloorCeiling.floor_le_ceil a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_of_int_eq
-- given
  (n : ℤ) :
-- imply
  ⌊(n : ℝ)⌋ = n := by
-- proof
  apply FloorCeiling.floor_of_int n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_of_int_eq
-- given
  (n : ℤ) :
-- imply
  ⌈(n : ℝ)⌉ = n := by
-- proof
  apply FloorCeiling.ceil_of_int n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_eq_ceil_of_int
-- given
  (n : ℤ) :
-- imply
  ⌊(n : ℝ)⌋ = ⌈(n : ℝ)⌉ := by
-- proof
  apply FloorCeiling.floor_eq_ceil_of_int n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma nat_div_eq_floor
-- given
  (n m : ℕ)
  (hm : m ≠ 0) :
-- imply
  n / m = Nat.floor ((n : ℚ) / m) := by
-- proof
  apply FloorCeiling.nat_div_eq_floor n m hm

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_add_int_eq
-- given
  (a : ℝ)
  (n : ℤ) :
-- imply
  ⌊a + n⌋ = ⌊a⌋ + n := by
-- proof
  apply FloorCeiling.floor_add_int a n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_add_int_eq
-- given
  (a : ℝ)
  (n : ℤ) :
-- imply
  ⌈a + n⌉ = ⌈a⌉ + n := by
-- proof
  apply FloorCeiling.ceil_add_int a n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_mono_le
  {a b : ℝ}
-- given
  (h : a ≤ b) :
-- imply
  ⌊a⌋ ≤ ⌊b⌋ := by
-- proof
  apply FloorCeiling.floor_mono h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_mono_le
  {a b : ℝ}
-- given
  (h : a ≤ b) :
-- imply
  ⌈a⌉ ≤ ⌈b⌉ := by
-- proof
  apply FloorCeiling.ceil_mono h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma fract_nonneg_le
-- given
  (a : ℝ) :
-- imply
  0 ≤ a - ⌊a⌋ := by
-- proof
  apply FloorCeiling.fract_nonneg a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma fract_lt_one
-- given
  (a : ℝ) :
-- imply
  a - ⌊a⌋ < 1 := by
-- proof
  apply FloorCeiling.fract_lt_one a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_eq_floor_add_one_iff
-- given
  (a : ℝ) :
-- imply
  ⌈a⌉ = ⌊a⌋ + 1 ↔ a ≠ ⌊a⌋ := by
-- proof
  apply FloorCeiling.ceil_eq_floor_add_one_iff a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_eq_ceil_iff
-- given
  (a : ℝ) :
-- imply
  ⌊a⌋ = ⌈a⌉ ↔ a = ⌊a⌋ := by
-- proof
  apply FloorCeiling.floor_eq_ceil_iff a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_size_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.parts.sum = n := by
-- proof
  apply Nat.Partition.size_eq p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_parts_pos_lt
  {n : ℕ}
-- given
  (p : Nat.Partition n)
  (i : ℕ)
  (hi : i ∈ p.parts) :
-- imply
  0 < i := by
-- proof
  apply Nat.Partition.parts_pos' p i hi

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_parts_le
  {n : ℕ}
-- given
  (p : Nat.Partition n)
  (i : ℕ)
  (hi : i ∈ p.parts) :
-- imply
  i ≤ n := by
-- proof
  apply Nat.Partition.parts_le p i hi

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_zero_parts_eq
-- given
  (p : Nat.Partition 0) :
-- imply
  p.parts = 0 := by
-- proof
  apply Nat.Partition.parts_eq_zero_of_partition_zero p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_parts_card_zero_eq
-- given
  (p : Nat.Partition 0) :
-- imply
  p.parts.card = 0 := by
-- proof
  apply Nat.Partition.parts_card_zero p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_indiscrete_parts_card_eq
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  (indiscrete n).parts.card = 1 := by
-- proof
  apply Nat.Partition.indiscrete_parts_card hn

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_indiscrete_parts_eq
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  (indiscrete n).parts = {n} := by
-- proof
  apply Nat.Partition.indiscrete_parts' hn

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_ofList_parts_eq
  {n : ℕ}
-- given
  (l : List ℕ)
  (hl_pos : ∀ i ∈ l, 0 < i)
  (hl_sum : l.sum = n) :
-- imply
  (ofList' l hl_pos hl_sum).parts = ↑l := by
-- proof
  apply Nat.Partition.ofList'_parts l hl_pos hl_sum

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_eq_iff_parts_iff
  {n : ℕ}
-- given
  (p q : Nat.Partition n) :
-- imply
  p = q ↔ p.parts = q.parts := by
-- proof
  apply Nat.Partition.eq_iff_parts_eq p q

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_le_sum_of_pos
-- given
  (s : Multiset ℕ)
  (h : ∀ i ∈ s, 0 < i) :
-- imply
  s.card ≤ s.sum := by
-- proof
  apply Nat.Partition.card_le_sum_of_pos s h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_fold_max_ge_of_mem_le
-- given
  (p : Multiset ℕ)
  (a : ℕ)
  (ha : a ∈ p) :
-- imply
  a ≤ p.fold max 0 := by
-- proof
  apply Nat.Partition.fold_max_ge_of_mem p a ha

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_filter_card_range_extend_eq
-- given
  (s : Multiset ℕ)
  (M N : ℕ)
  (hM : ∀ x ∈ s, x ≤ M)
  (hMN : M ≤ N) :
-- imply
  (Finset.range N).sum (fun i => (s.filter (· > i)).card) =
    (Finset.range M).sum (fun i => (s.filter (· > i)).card) := by
-- proof
  apply Nat.Partition.sum_filter_card_range_extend s M N hM hMN

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_range_filter_gt_eq
-- given
  (x M : ℕ) :
-- imply
  ((Finset.range M).filter (fun i => x > i)).card = min x M := by
-- proof
  apply Nat.Partition.card_range_filter_gt x M

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_filter_card_eq_sum
-- given
  (p : Multiset ℕ)
  (hp : ∀ i ∈ p, 0 < i) :
-- imply
  (Finset.range (p.fold max 0)).sum (fun i => (p.filter (· > i)).card) = p.sum := by
-- proof
  apply Nat.Partition.sum_filter_card_eq_sum p hp

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_filter_positive_eq
-- given
  (s : Multiset ℕ) :
-- imply
  (s.filter (· > 0)).sum = s.sum := by
-- proof
  apply Nat.Partition.sum_filter_positive s

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_zero_eq :
-- imply
  partitionCount 0 = 1 := by
-- proof
  apply Nat.Partition.partitionCount_zero

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_one_eq :
-- imply
  partitionCount 1 = 1 := by
-- proof
  apply Nat.Partition.partitionCount_one

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_pos_lt
-- given
  (n : ℕ) :
-- imply
  0 < partitionCount n := by
-- proof
  apply Nat.Partition.partitionCount_pos n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_eq_filter_numParts
-- given
  (k n : ℕ) :
-- imply
  partsCount k n = ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.numParts = k)).card := by
-- proof
  apply Nat.Partition.partsCount_eq_filter_numParts k n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_largestPart_le_iff_all_parts_le
  {n m : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.largestPart ≤ m ↔ ∀ i ∈ p.parts, i ≤ m := by
-- proof
  apply Nat.Partition.largestPart_le_iff_all_parts_le p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_filter_largestPart_le_eq_restricted
-- given
  (n m : ℕ) :
-- imply
  (Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.largestPart ≤ m) =
    restricted n (· ≤ m) := by
-- proof
  apply Nat.Partition.filter_largestPart_le_eq_restricted n m

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_numParts_zero_eq
-- given
  (p : Nat.Partition 0) :
-- imply
  p.numParts = 0 := by
-- proof
  apply Nat.Partition.numParts_zero p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_largestPart_zero_eq
-- given
  (p : Nat.Partition 0) :
-- imply
  p.largestPart = 0 := by
-- proof
  apply Nat.Partition.largestPart_zero p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_largestPart_le
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.largestPart ≤ n := by
-- proof
  apply Nat.Partition.largestPart_le p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_largestPart_pos_lt
  {n : ℕ}
-- given
  (hn : n > 0)
  (p : Nat.Partition n) :
-- imply
  0 < p.largestPart := by
-- proof
  apply Nat.Partition.largestPart_pos hn p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_numParts_le
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.numParts ≤ n := by
-- proof
  apply Nat.Partition.numParts_le p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_numParts_pos_lt
  {n : ℕ}
-- given
  (hn : n > 0)
  (p : Nat.Partition n) :
-- imply
  0 < p.numParts := by
-- proof
  apply Nat.Partition.numParts_pos hn p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_of_gt_eq
  {k n : ℕ}
-- given
  (h : k > n) :
-- imply
  partsCount k n = 0 := by
-- proof
  apply Nat.Partition.partsCount_of_gt h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_of_lt_eq
  {k n : ℕ}
-- given
  (h : n < k) :
-- imply
  partsCount k n = 0 := by
-- proof
  apply Nat.Partition.partsCount_of_gt' h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_zero_eq
-- given
  (n : ℕ) :
-- imply
  partsCount 0 n = if n = 0 then 1 else 0 := by
-- proof
  apply Nat.Partition.partsCount_zero n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_zero_left_eq
-- given
  (n : ℕ)
  (hn : n > 0) :
-- imply
  partsCount 0 n = 0 := by
-- proof
  apply Nat.Partition.partsCount_zero_left n hn

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_eq_zero_iff
-- given
  (k n : ℕ) :
-- imply
  partsCount k n = 0 ↔ k > n ∨ (k = 0 ∧ n > 0) := by
-- proof
  apply Nat.Partition.partsCount_eq_zero_iff k n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_one_eq
-- given
  (n : ℕ) :
-- imply
  partsCount 1 n = if n > 0 then 1 else 0 := by
-- proof
  apply Nat.Partition.partsCount_one n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_split_eq
  {k n : ℕ} :
-- imply
  partsCount k n = (partsWithOne k n).card + (partsWithoutOne k n).card := by
-- proof
  apply Nat.Partition.partsCount_split

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsWithOne_card_eq
  {k n : ℕ}
-- given
  (hk : k > 0)
  (hn : n > 0) :
-- imply
  (partsWithOne k n).card = partsCount (k - 1) (n - 1) := by
-- proof
  apply Nat.Partition.partsWithOne_card_eq hk hn

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsWithoutOne_card_eq
  {k n : ℕ}
-- given
  (hk : k > 0) :
-- imply
  (partsWithoutOne k n).card = partsCount k (n - k) := by
-- proof
  apply Nat.Partition.partsWithoutOne_card_eq hk

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_recurrence_eq
  {k n : ℕ}
-- given
  (hk : k > 0)
  (hn : n > 0) :
-- imply
  partsCount k n = partsCount k (n - k) + partsCount (k - 1) (n - 1) := by
-- proof
  apply Nat.Partition.partsCount_recurrence hk hn

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_two_parts_form
  {n : ℕ}
-- given
  (p : Nat.Partition n)
  (hp : p.parts.card = 2) :
-- imply
  ∃ b : ℕ, 1 ≤ b ∧ 2 * b ≤ n ∧ p.parts = {n - b, b} := by
-- proof
  apply Nat.Partition.partition_two_parts_form p hp

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_two_eq
-- given
  (n : ℕ) :
-- imply
  partsCount 2 n = n / 2 := by
-- proof
  apply Nat.Partition.partsCount_two n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_sum_eq
-- given
  (n : ℕ) :
-- imply
  partitionCount n = ∑ k ∈ Finset.range (n + 1), partsCount k n := by
-- proof
  apply Nat.Partition.partitionCount_sum n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_genFun
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R] :
-- imply
  HasProd (fun k => ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j))
    (PowerSeries.mk fun n => (partitionCount n : R)) := by
-- proof
  apply Nat.Partition.partitionCount_genFun

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_genFun_partsLeq
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (m : ℕ) :
-- imply
  HasProd (fun k => if k + 1 ≤ m then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1)
    (PowerSeries.mk fun n => (partsLeqCount m n : R)) := by
-- proof
  apply Nat.Partition.partitionCount_genFun_partsLeq m

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_genFun_partsLeq_finprod_eq
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (m : ℕ) :
-- imply
  (∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j))) =
    PowerSeries.mk fun n => ((restricted n (· ≤ m)).card : R) := by
-- proof
  apply Nat.Partition.partitionCount_genFun_partsLeq_finprod m

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsLeqCount_eq_coeff
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (m n : ℕ) :
-- imply
  ((restricted n (· ≤ m)).card : R) =
    (∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j))).coeff n := by
-- proof
  apply Nat.Partition.partsLeqCount_eq_coeff m n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_genFun_partsIn
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)] :
-- imply
  HasProd (fun k => if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1)
    (PowerSeries.mk fun n => (partsInCount I n : R)) := by
-- proof
  apply Nat.Partition.partitionCount_genFun_partsIn I

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsInCount_genFun_eq_tprod
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)] :
-- imply
  PowerSeries.mk (fun n => (partsInCount I n : R)) =
    tprod fun k => if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1 := by
-- proof
  apply Nat.Partition.partsInCount_genFun_eq_tprod I

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma multipliable_partsIn_genFun
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)] :
-- imply
  Multipliable (fun k => if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1) := by
-- proof
  apply Nat.Partition.multipliable_partsIn_genFun I

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_oddPartsCount_zero_eq :
-- imply
  oddPartsCount 0 = 1 := by
-- proof
  apply Nat.Partition.oddPartsCount_zero

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_distinctPartsCount_zero_eq :
-- imply
  distinctPartsCount 0 = 1 := by
-- proof
  apply Nat.Partition.distinctPartsCount_zero

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isOddParts_zero
-- given
  (p : Nat.Partition 0) :
-- imply
  p.IsOddParts := by
-- proof
  apply Nat.Partition.isOddParts_zero p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isDistinctParts_zero
-- given
  (p : Nat.Partition 0) :
-- imply
  p.IsDistinctParts := by
-- proof
  apply Nat.Partition.isDistinctParts_zero p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isOddParts_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.IsOddParts ↔ ∀ i ∈ p.parts, Odd i := by
-- proof
  apply Nat.Partition.isOddParts_iff p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isDistinctParts_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.IsDistinctParts ↔ p.parts.Nodup := by
-- proof
  apply Nat.Partition.isDistinctParts_iff p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isDistinctParts_count_le_one_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.IsDistinctParts ↔ ∀ i, p.parts.count i ≤ 1 := by
-- proof
  apply Nat.Partition.isDistinctParts_iff_count_le_one p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_mem_odds_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p ∈ odds n ↔ p.IsOddParts := by
-- proof
  apply Nat.Partition.mem_odds_iff p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_mem_distincts_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p ∈ distincts n ↔ p.IsDistinctParts := by
-- proof
  apply Nat.Partition.mem_distincts_iff p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_oddPartsCount_eq_filter_card
-- given
  (n : ℕ) :
-- imply
  oddPartsCount n = ((Finset.univ : Finset (Nat.Partition n)).filter IsOddParts).card := by
-- proof
  apply Nat.Partition.oddPartsCount_eq_filter_card n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_distinctPartsCount_eq_filter_card
-- given
  (n : ℕ) :
-- imply
  distinctPartsCount n = ((Finset.univ : Finset (Nat.Partition n)).filter IsDistinctParts).card := by
-- proof
  apply Nat.Partition.distinctPartsCount_eq_filter_card n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_odd_eq_distinct
-- given
  (n : ℕ) :
-- imply
  (odds n).card = (distincts n).card := by
-- proof
  apply Nat.Partition.odd_eq_distinct n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_oddPartsCount_eq_distinctPartsCount
-- given
  (n : ℕ) :
-- imply
  oddPartsCount n = distinctPartsCount n := by
-- proof
  apply Nat.Partition.oddPartsCount_eq_distinctPartsCount n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_isOddParts_eq_card_isDistinctParts
-- given
  (n : ℕ) :
-- imply
  ((Finset.univ : Finset (Nat.Partition n)).filter IsOddParts).card =
    ((Finset.univ : Finset (Nat.Partition n)).filter IsDistinctParts).card := by
-- proof
  apply Nat.Partition.card_isOddParts_eq_card_isDistinctParts n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sorted_countP_gt_iff
  {sl : List ℕ}
-- given
  (j : ℕ)
  (hsl : sl.Pairwise (· ≥ ·))
  (hj : j < sl.length)
  (i : ℕ) :
-- imply
  sl.countP (· > i) > j ↔ sl[j] > i := by
-- proof
  apply Nat.Partition.sorted_countP_gt_iff hsl j hj i

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_transpose_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.transpose.transpose = p := by
-- proof
  apply Nat.Partition.transpose_transpose p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_size_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.transpose.parts.sum = n := by
-- proof
  apply Nat.Partition.transpose_size p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_filter_card_pos_of_lt_largest
  {n : ℕ}
-- given
  (p : Nat.Partition n)
  (i : ℕ)
  (hi : i < p.parts.fold max 0) :
-- imply
  0 < (p.parts.filter (· > i)).card := by
-- proof
  apply Nat.Partition.filter_card_pos_of_lt_largest p i hi

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_length_eq_largestPart
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.transpose.numParts = p.largestPart := by
-- proof
  apply Nat.Partition.transpose_length_eq_largestPart p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_filter_gt_zero_card_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  (p.parts.filter (· > 0)).card = p.parts.card := by
-- proof
  apply Nat.Partition.filter_gt_zero_card_eq p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_largestPart_eq_length
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.transpose.largestPart = p.numParts := by
-- proof
  apply Nat.Partition.transpose_largestPart_eq_length p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_eq_largestPartCount
-- given
  (n k : ℕ) :
-- imply
  partsCount k n =
    ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.largestPart = k)).card := by
-- proof
  apply Nat.Partition.partsCount_eq_largestPartCount n k

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_sum_eq_largestPartLeq
-- given
  (n k : ℕ) :
-- imply
  ∑ i ∈ Finset.range (k + 1), partsCount i n =
    ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.largestPart ≤ k)).card := by
-- proof
  apply Nat.Partition.partsCount_sum_eq_largestPartLeq n k

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_sum_eq_partsLeqCount
-- given
  (n m : ℕ) :
-- imply
  ∑ k ∈ Finset.range (m + 1), partsCount k n = partsLeqCount m n := by
-- proof
  apply Nat.Partition.partsCount_sum_eq_partsLeqCount n m

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCountSum_genFun_eq
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (m : ℕ) :
-- imply
  PowerSeries.mk (fun n => (∑ k ∈ range (m + 1), partsCount k n : R)) =
    ∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j)) := by
-- proof
  apply Nat.Partition.partsCountSum_genFun m

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_symToPartsMultiset_pos
  {n : ℕ}
-- given
  (ℓ : ℕ)
  (hℓ : ℓ ≥ 1)
  (s : Sym (Fin ℓ) n) :
-- imply
  ∀ x ∈ symToPartsMultiset ℓ s, 0 < x := by
-- proof
  apply Nat.Partition.symToPartsMultiset_pos ℓ hℓ s

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_symToPartsMultiset_card_eq
  {n : ℕ}
-- given
  (ℓ : ℕ)
  (s : Sym (Fin ℓ) n) :
-- imply
  (symToPartsMultiset ℓ s).card = n + 1 := by
-- proof
  apply Nat.Partition.symToPartsMultiset_card ℓ s

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_symToPartsMultiset_fold_max_eq
  {n : ℕ}
-- given
  (ℓ : ℕ)
  (s : Sym (Fin ℓ) n) :
-- imply
  (symToPartsMultiset ℓ s).fold max 0 = ℓ := by
-- proof
  apply Nat.Partition.symToPartsMultiset_fold_max ℓ s

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_symToPartsMultiset_erase_eq
  {n : ℕ}
-- given
  (ℓ : ℕ)
  (s : Sym (Fin ℓ) n) :
-- imply
  (symToPartsMultiset ℓ s).erase ℓ = s.val.map (fun x => x.val + 1) := by
-- proof
  apply Nat.Partition.symToPartsMultiset_erase ℓ s

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_symToPartsMultiset_sum_range_is
-- given
  (k ℓ : ℕ)
  (hk : k ≥ 1)
  (hℓ : ℓ ≥ 1)
  (s : Sym (Fin ℓ) (k - 1)) :
-- imply
  (symToPartsMultiset ℓ s).sum ∈ Finset.Icc k (k * ℓ) := by
-- proof
  apply Nat.Partition.symToPartsMultiset_sum_range k ℓ hk hℓ s

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsAndLargestCountTotal_eq
-- given
  (k ℓ : ℕ)
  (hk : k ≥ 1)
  (hℓ : ℓ ≥ 1) :
-- imply
  partsAndLargestCountTotal k ℓ = (k + ℓ - 2).choose (k - 1) := by
-- proof
  apply Nat.Partition.partsAndLargestCountTotal_eq k ℓ hk hℓ

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_P_eq
-- given
  (n : ℕ) :
-- imply
  coeff n P = partitionCount n := by
-- proof
  apply Nat.Partition.coeff_P n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_S_eq
-- given
  (n : ℕ) :
-- imply
  coeff n S = if n = 0 then 0 else divisorSum n := by
-- proof
  apply Nat.Partition.coeff_S n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_X_mul_derivative_P_eq
-- given
  (n : ℕ) :
-- imply
  coeff n (X * derivative P) = n * coeff n P := by
-- proof
  apply Nat.Partition.coeff_X_mul_derivative_P n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_S_mul_P_eq
-- given
  (n : ℕ) :
-- imply
  coeff n (S * P) = ∑ k ∈ Finset.range n, divisorSum (k + 1) * partitionCount (n - k - 1) := by
-- proof
  apply Nat.Partition.coeff_S_mul_P n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_parts_as_weighted_count_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.parts.sum = (p.parts.toFinset).sum (fun d => d * p.parts.count d) := by
-- proof
  apply Nat.Partition.sum_parts_as_weighted_count p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_lhs_eq_sum_parts
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)]
  (n : ℕ) :
-- imply
  n * (restricted n (· ∈ I)).card =
    (restricted n (· ∈ I)).sum (fun p => p.parts.sum) := by
-- proof
  apply Nat.Partition.lhs_eq_sum_parts I n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_count_le_div_of_partition
-- given
  (n d : ℕ)
  (hd : 0 < d)
  (p : Nat.Partition n) :
-- imply
  p.parts.count d ≤ n / d := by
-- proof
  apply Nat.Partition.count_le_div_of_partition n d p hd

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_count_eq_sum_card_ge
-- given
  (n : ℕ)
  (s : Finset (Nat.Partition n))
  (d : ℕ) :
-- imply
  s.sum (fun p => p.parts.count d) =
    (Finset.range (n + 1)).sum (fun j =>
    (s.filter (fun p => p.parts.count d ≥ j + 1)).card) := by
-- proof
  apply Nat.Partition.sum_count_eq_sum_card_ge n s d

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_count_ge_eq_restricted
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)]
  (n d j : ℕ)
  (hI : ∀ i ∈ I, i > 0)
  (hd : d ∈ I)
  (hdj : d * j ≤ n) :
-- imply
  ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j)).card =
    (restricted (n - d * j) (· ∈ I)).card := by
-- proof
  apply Nat.Partition.card_count_ge_eq_restricted I hI n d j hd hdj

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_divisor_sum_reindex_eq
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)]
  (n : ℕ)
  (f : ℕ → ℕ) :
-- imply
  ∑ k ∈ Finset.range n, ∑ d ∈ (Nat.divisors (k + 1)).filter (· ∈ I), d * f (n - k - 1) =
    ∑ d ∈ (Finset.Icc 1 n).filter (· ∈ I),
    d * ∑ j ∈ Finset.Icc 1 (n / d), f (n - d * j) := by
-- proof
  apply Nat.Partition.divisor_sum_reindex I n f

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_divisorSum_restricted_eq
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)]
  (hI : ∀ i ∈ I, i > 0)
  (n : ℕ) :
-- imply
  n * (restricted n (· ∈ I)).card =
    ∑ k ∈ Finset.range n,
    (∑ d ∈ (Nat.divisors (k + 1)).filter (· ∈ I), d) *
    (restricted (n - k - 1) (· ∈ I)).card := by
-- proof
  apply Nat.Partition.partitionCount_divisorSum_restricted I hI n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_divisorSum_eq
-- given
  (n : ℕ) :
-- imply
  n * partitionCount n = ∑ k ∈ Finset.range n, divisorSum (k + 1) * partitionCount (n - k - 1) := by
-- proof
  apply Nat.Partition.partitionCount_divisorSum n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_X_mul_derivative_P_eq_S_mul_P :
-- imply
  X * derivative P = S * P := by
-- proof
  apply Nat.Partition.X_mul_derivative_P_eq_S_mul_P


-- created on 2026-10-11
