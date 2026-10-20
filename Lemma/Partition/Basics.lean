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
  {α : Type*} [Zero α] [One α] {P : Prop} [Decidable P] (h : P) :
-- imply
  (⦃P⦄ : α) = 1 :=
-- proof
  ite_eq_left h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_false_eq_zero
  {α : Type*} [Zero α] [One α] {P : Prop} [Decidable P] (h : ¬P) :
-- imply
  (⦃P⦄ : α) = 0 :=
-- proof
  ite_eq_right h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_eq_one_iff
  {α} [Zero α] [One α] [NeZero (1 : α)]
  {P : Prop} [Decidable P] :
-- imply
  (⦃P⦄ : α) = 1 ↔ P := by
-- proof
  constructor
  · intro h
    by_contra hn
    simp [iverson, hn] at h
  · intro h
    simp [h]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_eq_zero_iff
  {α} [Zero α] [One α] [NeZero (1 : α)]
  {P : Prop} [Decidable P] :
-- imply
  (⦃P⦄ : α) = 0 ↔ ¬P := by
-- proof
  constructor
  · intro h
    by_contra hn
    simp [iverson, hn] at h
  · intro h
    simp [h]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma kronecker_eq_iverson
  {α : Type*} [DecidableEq α] {R : Type*} [Zero R] [One R] (i j : α) :
-- imply
  (if i = j then (1 : R) else 0) = ⦃i = j⦄ :=
-- proof
  rfl

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_nat_eq_toNat
-- given
  (P : Prop) [Decidable P] :
-- imply
  (⦃P⦄ : ℕ) = (decide P).toNat := by
-- proof
  cases Decidable.em P with
  | inl h => simp [iverson, h]
  | inr h => simp [iverson, h]

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
  simp only [iverson, Finset.card_filter]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_and_eq
  {α} [MulZeroOneClass α]
  {P Q : Prop} [Decidable P] [Decidable Q] :
-- imply
  (⦃P ∧ Q⦄ : α) = ⦃P⦄ * ⦃Q⦄ := by
-- proof
  simp only [iverson]
  split_ifs <;> simp_all

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_sq_eq
  {α} [MonoidWithZero α]
  {P : Prop} [Decidable P] :
-- imply
  (⦃P⦄ : α) ^ 2 = ⦃P⦄ := by
-- proof
  simp only [iverson, sq]
  split_ifs <;> simp

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_not_eq
  {α} [Ring α] [NeZero (1 : α)]
  {P : Prop} [Decidable P] :
-- imply
  (⦃¬P⦄ : α) = 1 - ⦃P⦄ := by
-- proof
  simp only [iverson]
  split_ifs <;> simp_all

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_or_eq
  {α} [Ring α]
  {P Q : Prop} [Decidable P] [Decidable Q] :
-- imply
  (⦃P ∨ Q⦄ : α) = ⦃P⦄ + ⦃Q⦄ - ⦃P⦄ * ⦃Q⦄ := by
-- proof
  simp only [iverson]
  split_ifs <;> simp_all

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma iverson_imp_eq
  {α} [Ring α]
  {P Q : Prop} [Decidable P] [Decidable Q] :
-- imply
  (⦃P → Q⦄ : α) = 1 - ⦃P⦄ * (1 - ⦃Q⦄) := by
-- proof
  simp only [iverson]
  split_ifs <;> simp_all

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_def_iff
  (a : ℝ) (n : ℤ) :
-- imply
  n ≤ ⌊a⌋ ↔ n ≤ a :=
-- proof
  Int.le_floor

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_def_iff
  (a : ℝ) (n : ℤ) :
-- imply
  ⌈a⌉ ≤ n ↔ a ≤ n :=
-- proof
  Int.ceil_le

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_le
  (a : ℝ) :
-- imply
  (⌊a⌋ : ℝ) ≤ a :=
-- proof
  Int.floor_le a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma le_ceil
  (a : ℝ) :
-- imply
  a ≤ ⌈a⌉ :=
-- proof
  Int.le_ceil a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_le_ceil
  (a : ℝ) :
-- imply
  ⌊a⌋ ≤ ⌈a⌉ :=
-- proof
  Int.floor_le_ceil a

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_of_int_eq
  (n : ℤ) :
-- imply
  ⌊(n : ℝ)⌋ = n :=
-- proof
  Int.floor_intCast n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_of_int_eq
  (n : ℤ) :
-- imply
  ⌈(n : ℝ)⌉ = n :=
-- proof
  Int.ceil_intCast n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_eq_ceil_of_int
-- given
  (n : ℤ) :
-- imply
  ⌊(n : ℝ)⌋ = ⌈(n : ℝ)⌉ := by
-- proof
  rw [floor_of_int_eq, ceil_of_int_eq]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma nat_div_eq_floor
-- given
  (n m : ℕ)
  (hm : m ≠ 0) :
-- imply
  n / m = Nat.floor ((n : ℚ) / m) := by
-- proof
  have : NeZero m := ⟨hm⟩
  have h : Nat.floor ((n : ℚ) / ((m : ℕ) : ℚ)) = n / m := Nat.floor_div_eq_div (K := ℚ) n m
  exact h.symm

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_add_int_eq
  (a : ℝ) (n : ℤ) :
-- imply
  ⌊a + n⌋ = ⌊a⌋ + n :=
-- proof
  Int.floor_add_intCast a n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_add_int_eq
  (a : ℝ) (n : ℤ) :
-- imply
  ⌈a + n⌉ = ⌈a⌉ + n :=
-- proof
  Int.ceil_add_intCast a n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_mono_le
  {a b : ℝ} (h : a ≤ b) :
-- imply
  ⌊a⌋ ≤ ⌊b⌋ :=
-- proof
  Int.floor_mono h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_mono_le
  {a b : ℝ} (h : a ≤ b) :
-- imply
  ⌈a⌉ ≤ ⌈b⌉ :=
-- proof
  Int.ceil_mono h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma fract_nonneg_le
-- given
  (a : ℝ) :
-- imply
  0 ≤ a - ⌊a⌋ := by
-- proof
  have h := Int.fract_nonneg a
  simp only [Int.fract] at h
  exact h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma fract_lt_one
-- given
  (a : ℝ) :
-- imply
  a - ⌊a⌋ < 1 := by
-- proof
  have h := Int.fract_lt_one a
  simp only [Int.fract] at h
  exact h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma ceil_eq_floor_add_one_iff
-- given
  (a : ℝ) :
-- imply
  ⌈a⌉ = ⌊a⌋ + 1 ↔ a ≠ ⌊a⌋ := by
-- proof
  constructor
  · intro h hcontra
    have h1 : ⌈a⌉ = ⌊a⌋ := by
      have : a = (⌊a⌋ : ℝ) := hcontra
      rw [this, Int.ceil_intCast, Int.floor_intCast]
    omega
  · intro h
    have h1 : (⌊a⌋ : ℝ) < a := by
      by_contra hle
      push Not at hle
      have heq : a = ⌊a⌋ := le_antisymm hle (Int.floor_le a)
      exact h heq
    have h2 : ⌊a⌋ + 1 ≤ ⌈a⌉ := by
      rw [Int.add_one_le_iff, Int.lt_ceil]
      exact h1
    have h3 : ⌈a⌉ ≤ ⌊a⌋ + 1 := by
      have : a < ⌊a⌋ + 1 := Int.lt_floor_add_one a
      rw [Int.ceil_le]
      push_cast
      exact le_of_lt this
    omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma floor_eq_ceil_iff
-- given
  (a : ℝ) :
-- imply
  ⌊a⌋ = ⌈a⌉ ↔ a = ⌊a⌋ := by
-- proof
  constructor
  · intro h
    by_contra hne
    have := ceil_eq_floor_add_one_iff a |>.mpr hne
    omega
  · intro h
    rw [h, Int.floor_intCast, Int.ceil_intCast]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_size_eq
  {n : ℕ} (p : Nat.Partition n) :
-- imply
  p.parts.sum = n :=
-- proof
  p.parts_sum

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_parts_pos_lt
  {n : ℕ} (p : Nat.Partition n) (i : ℕ) (hi : i ∈ p.parts) :
-- imply
  0 < i :=
-- proof
  p.parts_pos hi

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
  calc i ≤ p.parts.sum := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hi
    _ = n := p.parts_sum

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_zero_parts_eq
  (p : Nat.Partition 0) :
-- imply
  p.parts = 0 :=
-- proof
  partition_zero_parts p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_parts_card_zero_eq
-- given
  (p : Nat.Partition 0) :
-- imply
  p.parts.card = 0 := by
-- proof
  simp only [partition_zero_parts, Multiset.card_zero]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_indiscrete_parts_card_eq
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  (indiscrete n).parts.card = 1 := by
-- proof
  simp only [indiscrete_parts hn, Multiset.card_singleton]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_indiscrete_parts_eq
  {n : ℕ} (hn : n ≠ 0) :
-- imply
  (indiscrete n).parts = {n} :=
-- proof
  indiscrete_parts hn

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_ofList_parts_eq
  {n : ℕ} (l : List ℕ) (hl_pos : ∀ i ∈ l, 0 < i) (hl_sum : l.sum = n) :
-- imply
  (ofList' l hl_pos hl_sum).parts = ↑l :=
-- proof
  rfl

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_eq_iff_parts_iff
  {n : ℕ}
-- given
  (p q : Nat.Partition n) :
-- imply
  p = q ↔ p.parts = q.parts := by
-- proof
  constructor
  · intro h; rw [h]
  · intro h; exact Nat.Partition.ext_iff.mpr h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_le_sum_of_pos
-- given
  (s : Multiset ℕ)
  (h : ∀ i ∈ s, 0 < i) :
-- imply
  s.card ≤ s.sum := by
-- proof
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, Multiset.sum_cons]
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ i ∈ s, 0 < i := fun i hi => h i (Multiset.mem_cons_of_mem hi)
    have ihs := ih hs
    omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_fold_max_ge_of_mem_le
  (p : Multiset ℕ) (a : ℕ) (ha : a ∈ p) :
-- imply
  a ≤ p.fold max 0 := by
-- proof
  induction p using Multiset.induction with
  | empty => simp at ha
  | cons b s ih =>
    simp only [Multiset.fold_cons_left]
    simp only [Multiset.mem_cons] at ha
    rcases ha with rfl | ha
    · exact le_max_left a (Multiset.fold max 0 s)
    · exact le_trans (ih ha) (le_max_right b (Multiset.fold max 0 s))

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
  have h := Finset.sum_range_add_sum_Ico (fun i => (s.filter (· > i)).card) hMN
  rw [← h]
  suffices hzero : ∑ i ∈ Finset.Ico M N, (s.filter (· > i)).card = 0 by linarith
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_Ico] at hi
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx
  simp only [gt_iff_lt, not_lt]
  exact le_trans (hM x hx) hi.1

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_range_filter_gt_eq
-- given
  (x M : ℕ) :
-- imply
  ((Finset.range M).filter (fun i => x > i)).card = min x M := by
-- proof
  simp only [gt_iff_lt]
  rw [← Finset.card_range (min x M)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_filter_card_eq_sum
-- given
  (p : Multiset ℕ)
  (hp : ∀ i ∈ p, 0 < i) :
-- imply
  (Finset.range (p.fold max 0)).sum (fun i => (p.filter (· > i)).card) = p.sum := by
-- proof
  induction p using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hs : ∀ i ∈ s, 0 < i := fun i hi => hp i (Multiset.mem_cons_of_mem hi)
    have ha : 0 < a := hp a (Multiset.mem_cons_self a s)
    specialize ih hs
    simp only [Multiset.sum_cons, Multiset.fold_cons_left]
    let M := s.fold max 0
    conv_lhs =>
      arg 2
      ext i
      rw [Multiset.filter_cons]
    have hcard : ∀ i, ((if a > i then {a} else 0) + s.filter (· > i)).card =
                      (if a > i then 1 else 0) + (s.filter (· > i)).card := by
      intro i
      split_ifs with h
      · simp only [Multiset.singleton_add, Multiset.card_cons]; ring
      · simp only [zero_add]
    simp_rw [hcard]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i ∈ Finset.range (max a M), (if a > i then 1 else 0) = a := by
      rw [Finset.sum_boole, Nat.cast_id]
      convert partition_card_range_filter_gt_eq a (max a M) using 2
      simp only [le_max_iff, le_refl, true_or, min_eq_left]
    rw [h1]
    have hbound : ∀ x ∈ s, x ≤ M := fun x hx => partition_fold_max_ge_of_mem_le s x hx
    have h2 : (Finset.range (max a M)).sum (fun i => (s.filter (· > i)).card) =
              (Finset.range M).sum (fun i => (s.filter (· > i)).card) := by
      apply partition_sum_filter_card_range_extend_eq s M (max a M) hbound (le_max_right a M)
    rw [h2, ih]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_filter_positive_eq
-- given
  (s : Multiset ℕ) :
-- imply
  (s.filter (· > 0)).sum = s.sum := by
-- proof
  have h := @Multiset.sum_filter_add_sum_filter_not ℕ _ s (· > 0) _
  simp only [gt_iff_lt, Nat.not_lt, Nat.le_zero] at h
  suffices hz : (s.filter (· = 0)).sum = 0 by linarith
  rw [Multiset.sum_eq_zero_iff]
  intro x hx
  simp only [Multiset.mem_filter] at hx
  exact hx.2

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_zero_eq :
-- imply
  partitionCount 0 = 1 := by
-- proof
  simp only [partitionCount]
  rfl

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_one_eq :
-- imply
  partitionCount 1 = 1 := by
-- proof
  native_decide

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_pos_lt
-- given
  (n : ℕ) :
-- imply
  0 < partitionCount n := by
-- proof
  simp only [partitionCount]
  exact Fintype.card_pos

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_eq_filter_numParts
-- given
  (k n : ℕ) :
-- imply
  partsCount k n = ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.numParts = k)).card := by
-- proof
  simp only [partsCount, numParts]
  rfl

private lemma partition_fold_max_le_of_all_le_prime
  (s : Multiset ℕ) (m : ℕ) (h : ∀ i ∈ s, i ≤ m) :
-- imply
  s.fold max 0 ≤ m := by
-- proof
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.fold_cons_left]
    have ha : a ≤ m := h a (Multiset.mem_cons_self a t)
    have ht : ∀ i ∈ t, i ≤ m := fun i hi => h i (Multiset.mem_cons_of_mem hi)
    exact max_le ha (ih ht)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_largestPart_le_iff_all_parts_le
  {n m : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.largestPart ≤ m ↔ ∀ i ∈ p.parts, i ≤ m := by
-- proof
  unfold largestPart
  constructor
  · intro h i hi
    exact le_trans (partition_fold_max_ge_of_mem_le p.parts i hi) h
  · intro h
    exact partition_fold_max_le_of_all_le_prime p.parts m h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_filter_largestPart_le_eq_restricted
-- given
  (n m : ℕ) :
-- imply
  (Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.largestPart ≤ m) =
    restricted n (· ≤ m) := by
-- proof
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, restricted]
  exact partition_largestPart_le_iff_all_parts_le p

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_numParts_zero_eq
-- given
  (p : Nat.Partition 0) :
-- imply
  p.numParts = 0 := by
-- proof
  simp only [numParts, partition_zero_parts, Multiset.card_zero]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_largestPart_zero_eq
-- given
  (p : Nat.Partition 0) :
-- imply
  p.largestPart = 0 := by
-- proof
  simp only [largestPart, partition_zero_parts, Multiset.fold_zero]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_largestPart_le
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.largestPart ≤ n := by
-- proof
  rw [partition_largestPart_le_iff_all_parts_le]
  exact fun i hi => partition_parts_le p i hi

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
  unfold largestPart
  have hne : p.parts ≠ 0 := by
    intro h
    have := p.parts_sum
    simp only [h, Multiset.sum_zero] at this
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  have hxpos := p.parts_pos hx
  exact lt_of_lt_of_le hxpos (partition_fold_max_ge_of_mem_le p.parts x hx)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_numParts_le
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.numParts ≤ n := by
-- proof
  simp only [numParts]
  calc p.parts.card ≤ p.parts.sum := partition_card_le_sum_of_pos p.parts (fun i hi => p.parts_pos hi)
    _ = n := p.parts_sum

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
  simp only [numParts]
  by_contra hc
  simp only [not_lt, Nat.le_zero, Multiset.card_eq_zero] at hc
  have h := p.parts_sum
  simp only [hc, Multiset.sum_zero] at h
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_of_gt_eq
  {k n : ℕ}
-- given
  (h : k > n) :
-- imply
  partsCount k n = 0 := by
-- proof
  simp only [partsCount, filter_eq_empty_iff, Finset.card_eq_zero]
  intro p _
  have hle : Multiset.card p.parts ≤ p.parts.sum :=
    partition_card_le_sum_of_pos p.parts (fun i hi => p.parts_pos hi)
  have hsum : Multiset.card p.parts ≤ n := by
    calc Multiset.card p.parts ≤ p.parts.sum := hle
      _ = n := p.parts_sum
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_of_lt_eq
  {k n : ℕ} (h : n < k) :
-- imply
  partsCount k n = 0 :=
-- proof
  partition_partsCount_of_gt_eq h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_zero_eq
-- given
  (n : ℕ) :
-- imply
  partsCount 0 n = if n = 0 then 1 else 0 := by
-- proof
  simp only [partsCount]
  split_ifs with hn
  · subst hn
    have huniv : (Finset.univ : Finset (Nat.Partition 0)).filter
        (fun p => Multiset.card p.parts = 0) = Finset.univ := by
      ext p
      simp only [Finset.mem_filter, mem_univ, true_and, partition_zero_parts, Multiset.card_zero]
    simp only [huniv]
    rfl
  · rw [Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _
    have hp : p.parts.sum = n := p.parts_sum
    by_contra hc
    simp only [Multiset.card_eq_zero] at hc
    simp only [hc, Multiset.sum_zero] at hp
    exact hn hp.symm

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_zero_left_eq
-- given
  (n : ℕ)
  (hn : n > 0) :
-- imply
  partsCount 0 n = 0 := by
-- proof
  rw [partition_partsCount_zero_eq]
  simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_eq_zero_iff
-- given
  (k n : ℕ) :
-- imply
  partsCount k n = 0 ↔ k > n ∨ (k = 0 ∧ n > 0) := by
-- proof
  constructor
  · -- Forward direction: if partsCount k n = 0, then k > n or (k = 0 ∧ n > 0)
    intro h
    by_contra hc
    push Not at hc
    obtain ⟨hkn, hk0⟩ := hc
    -- We have k ≤ n and (k ≠ 0 or n = 0)
    rcases Nat.eq_zero_or_pos k with hk | hkpos
    · -- k = 0
      subst hk
      -- n = 0 since k = 0 → n ≤ 0 from hk0, and n : ℕ
      have hn0 : n = 0 := Nat.le_zero.mp (hk0 rfl)
      -- But partsCount 0 0 = 1 ≠ 0
      subst hn0
      simp only [partition_partsCount_zero_eq, ↓reduceIte] at h
      exact Nat.one_ne_zero h
    · -- k > 0, and k ≤ n
      -- There exists a partition of n into k parts: (1, 1, ..., 1, n - k + 1)
      -- The partition (1, 1, ..., 1, n - k + 1) has k parts and sums to n
      let parts : Multiset ℕ := Multiset.replicate (k - 1) 1 + {n - k + 1}
      have hparts_card : parts.card = k := by
        simp only [parts, Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]
        omega
      have hparts_sum : parts.sum = n := by
        simp only [parts, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton,
                   smul_eq_mul, mul_one]
        omega
      have hparts_pos : ∀ x ∈ parts, 0 < x := by
        intro x hx
        simp only [parts, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton] at hx
        cases hx with
        | inl h => exact h.2 ▸ Nat.one_pos
        | inr h => omega
      let p : Nat.Partition n := { parts := parts, parts_sum := hparts_sum, parts_pos := @hparts_pos }
      have hp_mem : p ∈ (Finset.univ : Finset (Nat.Partition n)).filter
          (fun q => Multiset.card q.parts = k) := by
        simp only [Finset.mem_filter, mem_univ, true_and, p]
        exact hparts_card
      simp only [partsCount, Finset.card_eq_zero] at h
      rw [h] at hp_mem
      simp at hp_mem
  · -- Backward direction: if k > n or (k = 0 ∧ n > 0), then partsCount k n = 0
    intro h
    cases h with
    | inl hkn => exact partition_partsCount_of_gt_eq hkn
    | inr hk0 =>
      obtain ⟨hk, hn⟩ := hk0
      subst hk
      rw [partition_partsCount_zero_eq]
      simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_one_eq
-- given
  (n : ℕ) :
-- imply
  partsCount 1 n = if n > 0 then 1 else 0 := by
-- proof
  simp only [partsCount]
  split_ifs with hn
  · -- For n > 0, there's exactly one partition into 1 part: (n)
    have h : (Finset.univ : Finset (Nat.Partition n)).filter
        (fun p => Multiset.card p.parts = 1) = {indiscrete n} := by
      ext p
      simp only [Finset.mem_filter, mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hcard
        ext
        have hp_sum : p.parts.sum = n := p.parts_sum
        rw [Multiset.card_eq_one] at hcard
        obtain ⟨a, ha⟩ := hcard
        simp only [ha, Multiset.sum_singleton] at hp_sum
        subst hp_sum
        simp only [ha, indiscrete_parts (Nat.pos_iff_ne_zero.mp hn)]
      · intro heq
        rw [heq, indiscrete_parts (Nat.pos_iff_ne_zero.mp hn)]
        simp only [Multiset.card_singleton]
    rw [h]
    simp only [Finset.card_singleton]
  · -- For n = 0, there are no partitions into 1 part
    push Not at hn
    interval_cases n
    rw [Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _
    simp only [partition_zero_parts, Multiset.card_zero]
    omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsWithOne_disjoint_partsWithoutOne
  {k n : ℕ} :
-- imply
  Disjoint (partsWithOne k n) (partsWithoutOne k n) := by
-- proof
  rw [Finset.disjoint_iff_ne]
  intro p hp q hq heq
  simp only [partsWithOne, partsWithoutOne, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  rw [heq] at hp
  exact hq.2 hp.2

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsWithOne_union_partsWithoutOne_eq
  {k n : ℕ} :
-- imply
  partsWithOne k n ∪ partsWithoutOne k n = (Finset.univ : Finset (Nat.Partition n)).filter fun p => p.parts.card = k := by
-- proof
  ext p
  simp only [partsWithOne, partsWithoutOne, Finset.mem_union, Finset.mem_filter,
             Finset.mem_univ, true_and]
  constructor
  · intro h; rcases h with ⟨hk, _⟩ | ⟨hk, _⟩ <;> exact hk
  · intro hk'; by_cases h : containsOne p
    · left; exact ⟨hk', h⟩
    · right; exact ⟨hk', h⟩

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_split_eq
  {k n : ℕ} :
-- imply
  partsCount k n = (partsWithOne k n).card + (partsWithoutOne k n).card := by
-- proof
  simp only [partsCount]
  rw [← Finset.card_union_of_disjoint partition_partsWithOne_disjoint_partsWithoutOne]
  congr 1
  exact partition_partsWithOne_union_partsWithoutOne_eq.symm

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_ge_card_of_all_pos
  {s : Multiset ℕ} (h : ∀ x ∈ s, x > 0) :
-- imply
  s.sum ≥ s.card := by
-- proof
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha : a > 0 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, x > 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have := ih ht
    omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_map_sub_one_eq
  {s : Multiset ℕ} (h : ∀ x ∈ s, x > 1) :
-- imply
  (s.map (· - 1)).sum = s.sum - s.card := by
-- proof
  have hpos : ∀ x ∈ s, x > 0 := fun x hx => Nat.lt_trans Nat.zero_lt_one (h x hx)
  have hge : s.sum ≥ s.card := partition_sum_ge_card_of_all_pos hpos
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : a > 1 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, x > 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have htpos : ∀ x ∈ t, x > 0 := fun x hx => Nat.lt_trans Nat.zero_lt_one (ht x hx)
    have htge : t.sum ≥ t.card := partition_sum_ge_card_of_all_pos htpos
    rw [ih ht htpos htge]
    omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_filter_ne_zero_of_all_pos_eq
  {s : Multiset ℕ} (h : ∀ x ∈ s, x > 0) :
-- imply
  s.filter (· ≠ 0) = s := by
-- proof
  rw [Multiset.filter_eq_self]
  intro x hx
  exact Nat.pos_iff_ne_zero.mp (h x hx)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_removeOne_parts_eq
-- given
  {n : ℕ}
  (p : Nat.Partition n)
  (h : 1 ∈ p.parts) :
-- imply
  (removeOne p h).parts = p.parts.erase 1 := by
-- proof
  simp only [removeOne, Nat.Partition.ofSums]
  apply partition_filter_ne_zero_of_all_pos_eq
  intro x hx
  exact p.parts_pos (Multiset.erase_subset 1 p.parts hx)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_removeOne_parts_card_eq
-- given
  {n : ℕ}
  (p : Nat.Partition n)
  (h : 1 ∈ p.parts) :
-- imply
  (removeOne p h).parts.card = p.parts.card - 1 := by
-- proof
  rw [partition_removeOne_parts_eq, Multiset.card_erase_of_mem h]
  simp only [Nat.pred_eq_sub_one]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_addOne_parts_eq
-- given
  {n : ℕ}
  (p : Nat.Partition n) :
-- imply
  (addOne p).parts = Multiset.cons 1 p.parts := by
-- proof
  simp only [addOne, Nat.Partition.ofSums]
  rw [Multiset.filter_cons_of_pos]
  · congr 1
    apply partition_filter_ne_zero_of_all_pos_eq
    intro x hx
    exact p.parts_pos hx
  · decide

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_addOne_parts_card_eq
-- given
  {n : ℕ}
  (p : Nat.Partition n) :
-- imply
  (addOne p).parts.card = p.parts.card + 1 := by
-- proof
  rw [partition_addOne_parts_eq]
  simp only [Multiset.card_cons]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_addOne_containsOne
-- given
  {n : ℕ}
  (p : Nat.Partition n) :
-- imply
  containsOne (addOne p) := by
-- proof
  simp only [containsOne, partition_addOne_parts_eq, Multiset.mem_cons, true_or]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_map_sub_one_injective
  {s t : Multiset ℕ} (hs : ∀ x ∈ s, x > 1) (ht : ∀ x ∈ t, x > 1) (h : s.map (· - 1) = t.map (· - 1)) :
-- imply
  s = t := by
-- proof
  have key : ∀ (m : Multiset ℕ), (∀ x ∈ m, x > 1) → (m.map (· - 1)).map (· + 1) = m := by
    intro m hm
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id m]
    apply Multiset.map_congr rfl
    intro x hx
    simp only [Function.comp_apply, id_eq]
    have : x > 1 := hm x hx
    omega
  calc s = (s.map (· - 1)).map (· + 1) := (key s hs).symm
    _ = (t.map (· - 1)).map (· + 1) := by rw [h]
    _ = t := key t ht

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_subtractOneFromEach_parts_eq
-- given
  {n k : ℕ}
  (p : Nat.Partition n)
  (hk : p.parts.card = k)
  (h : ∀ x ∈ p.parts, x > 1) :
-- imply
  (subtractOneFromEach p hk h).parts = p.parts.map (· - 1) := by
-- proof
  simp only [subtractOneFromEach, Nat.Partition.ofSums]
  apply partition_filter_ne_zero_of_all_pos_eq
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : y > 1 := h y hy
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_subtractOneFromEach_parts_card_eq
-- given
  {n k : ℕ}
  (p : Nat.Partition n)
  (hk : p.parts.card = k)
  (h : ∀ x ∈ p.parts, x > 1) :
-- imply
  (subtractOneFromEach p hk h).parts.card = k := by
-- proof
  rw [partition_subtractOneFromEach_parts_eq, Multiset.card_map, hk]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_addOneToEach_parts_eq
-- given
  {n k : ℕ}
  (p : Nat.Partition n)
  (hk : p.parts.card = k) :
-- imply
  (addOneToEach p hk).parts = p.parts.map (· + 1) := by
-- proof
  simp only [addOneToEach, Nat.Partition.ofSums]
  apply partition_filter_ne_zero_of_all_pos_eq
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : y > 0 := p.parts_pos hy
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_addOneToEach_parts_card_eq
-- given
  {n k : ℕ}
  (p : Nat.Partition n)
  (hk : p.parts.card = k) :
-- imply
  (addOneToEach p hk).parts.card = k := by
-- proof
  rw [partition_addOneToEach_parts_eq, Multiset.card_map, hk]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_castPartition_parts
  {n m : ℕ} (h : n = m) (p : Nat.Partition n) :
-- imply
  (castPartition h p).parts = p.parts :=
-- proof
  rfl

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
  simp only [partsWithOne, partsCount]
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  apply Finset.card_bij (fun p hp => by
    have hmem := Finset.mem_filter.mp hp
    exact removeOne p hmem.2.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [partition_removeOne_parts_card_eq]; omega
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    ext
    have h1 : (removeOne p₁ hp₁.2).parts = (removeOne p₂ hp₂.2).parts := by rw [heq]
    simp only [partition_removeOne_parts_eq] at h1
    rw [← Multiset.cons_erase hp₁.2, ← Multiset.cons_erase hp₂.2, h1]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    let p' := addOne q
    let p := castPartition hn_eq p'
    have hp'_parts : p'.parts = 1 ::ₘ q.parts := partition_addOne_parts_eq q
    have h1mem : 1 ∈ p.parts := by
      simp only [p, partition_castPartition_parts, hp'_parts]
      exact Multiset.mem_cons_self 1 q.parts
    refine ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, h1mem⟩
      have hp'_card : p'.parts.card = q.parts.card + 1 := partition_addOne_parts_card_eq q
      simp only [p, partition_castPartition_parts, hp'_card, hq]; omega
    · ext
      simp only [partition_removeOne_parts_eq, p, partition_castPartition_parts, hp'_parts, Multiset.erase_cons_head]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsWithoutOne_card_eq
  {k n : ℕ}
-- given
  (hk : k > 0) :
-- imply
  (partsWithoutOne k n).card = partsCount k (n - k) := by
-- proof
  simp only [partsWithoutOne, partsCount]
  by_cases hn : n < k
  · -- When n < k, both sides are 0
    have h1 : ((Finset.univ : Finset (Nat.Partition n)).filter
        fun p => p.parts.card = k ∧ ¬containsOne p).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _
      simp only [not_and, not_not]
      intro hcard
      have hsum : p.parts.sum ≥ k := by
        calc p.parts.sum ≥ p.parts.card := partition_sum_ge_card_of_all_pos (fun x hx => p.parts_pos hx)
          _ = k := hcard
      have : p.parts.sum = n := p.parts_sum
      omega
    have h2 : ((Finset.univ : Finset (Nat.Partition (n - k))).filter
        fun p => p.parts.card = k).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hcard
      have hsum : p.parts.sum ≥ k := by
        calc p.parts.sum ≥ p.parts.card := partition_sum_ge_card_of_all_pos (fun x hx => p.parts_pos hx)
          _ = k := hcard
      have : p.parts.sum = n - k := p.parts_sum
      have : n - k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hn)
      omega
    rw [h1, h2]
  · -- When n ≥ k
    push Not at hn
    have hn_eq : n - k + k = n := Nat.sub_add_cancel hn
    apply Finset.card_bij (fun p hp => by
      have hmem := Finset.mem_filter.mp hp
      have hno1 : ∀ x ∈ p.parts, x > 1 := by
        intro x hx
        have hpos := p.parts_pos hx
        have hne1 : x ≠ 1 := fun heq => by rw [heq] at hx; exact hmem.2.2 hx
        omega
      exact subtractOneFromEach p hmem.2.1 hno1)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hno1 : ∀ x ∈ p.parts, x > 1 := by
        intro x hx
        have hpos := p.parts_pos hx
        have hne1 : x ≠ 1 := fun heq => by rw [heq] at hx; exact hp.2 hx
        omega
      exact partition_subtractOneFromEach_parts_card_eq p hp.1 hno1
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
      have hno1₁ : ∀ x ∈ p₁.parts, x > 1 := by
        intro x hx
        have hpos := p₁.parts_pos hx
        have hne1 : x ≠ 1 := fun h => by rw [h] at hx; exact hp₁.2 hx
        omega
      have hno1₂ : ∀ x ∈ p₂.parts, x > 1 := by
        intro x hx
        have hpos := p₂.parts_pos hx
        have hne1 : x ≠ 1 := fun h => by rw [h] at hx; exact hp₂.2 hx
        omega
      ext
      have h1 : (subtractOneFromEach p₁ hp₁.1 hno1₁).parts =
                (subtractOneFromEach p₂ hp₂.1 hno1₂).parts := by rw [heq]
      simp only [partition_subtractOneFromEach_parts_eq] at h1
      rw [partition_map_sub_one_injective hno1₁ hno1₂ h1]
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      let p' := addOneToEach q hq
      let p := castPartition hn_eq p'
      have hp'_parts : p'.parts = q.parts.map (· + 1) := partition_addOneToEach_parts_eq q hq
      have hno1 : ∀ x ∈ p.parts, x > 1 := by
        intro x hx
        simp only [p, partition_castPartition_parts, hp'_parts, Multiset.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have : y > 0 := q.parts_pos hy
        omega
      have hp_card : p.parts.card = k := by
        simp only [p, partition_castPartition_parts]; exact partition_addOneToEach_parts_card_eq q hq
      have hp_no1 : ¬containsOne p := by
        simp only [containsOne, p, partition_castPartition_parts, hp'_parts, Multiset.mem_map]
        intro ⟨y, hy, heq⟩
        have : y > 0 := q.parts_pos hy
        omega
      refine ⟨p, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp_card, hp_no1⟩
      · have heq_parts : (subtractOneFromEach p hp_card hno1).parts = q.parts := by
          simp only [partition_subtractOneFromEach_parts_eq, p, partition_castPartition_parts, hp'_parts,
                     Multiset.map_map, Function.comp]
          conv_rhs => rw [← Multiset.map_id q.parts]
          apply Multiset.map_congr rfl
          intro x hx
          simp only [id_eq]
          have : x > 0 := q.parts_pos hx
          omega
        ext; rw [heq_parts]

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
  rw [partition_partsCount_split_eq, add_comm]
  congr 1
  · exact partition_partsWithoutOne_card_eq hk
  · exact partition_partsWithOne_card_eq hk hn

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_two_parts_form_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n)
  (hp : p.parts.card = 2) :
-- imply
  ∃ b : ℕ, 1 ≤ b ∧ 2 * b ≤ n ∧ p.parts = {n - b, b} := by
-- proof
  rw [Multiset.card_eq_two] at hp
  obtain ⟨a, b, hab⟩ := hp
  wlog h : b ≤ a generalizing a b
  · push Not at h
    have hab' : p.parts = {b, a} := by
      rw [hab]; ext x
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      split_ifs <;> omega
    exact this b a hab' (le_of_lt h)
  have hsum : a + b = n := by
    have := p.parts_sum; rw [hab] at this; simp at this; omega
  have hb_pos : 0 < b := p.parts_pos (by rw [hab]; simp)
  use b
  refine ⟨by omega, by omega, ?_⟩
  rw [hab]; congr 1; omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_fold_min_of_two_multiset_eq
  (a b n : ℕ) (h : a + b ≤ n) :
-- imply
  ({a, b} : Multiset ℕ).fold min n = min a b := by
-- proof
  simp only [Multiset.insert_eq_cons, Multiset.fold_cons_left, Multiset.fold_singleton]
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_smallerPartOf_spec
  {n : ℕ} (p : Nat.Partition n) (hp : p.parts.card = 2) :
-- imply
  let b := smallerPartOf p hp
  1 ≤ b ∧ 2 * b ≤ n ∧ p.parts = {n - b, b} := by
-- proof
  obtain ⟨b, hb1, hb2, hparts⟩ := partition_two_parts_form_eq p hp
  simp only [smallerPartOf, hparts]
  have hsum : (n - b) + b = n := by omega
  rw [partition_fold_min_of_two_multiset_eq _ _ _ (le_of_eq hsum)]
  have hmin : min (n - b) b = b := by omega
  simp only [hmin]
  exact ⟨hb1, hb2, trivial⟩

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_ofSmallerPart_parts
-- given
  (n b : ℕ)
  (hb1 : 1 ≤ b)
  (hb2 : 2 * b ≤ n) :
-- imply
  (ofSmallerPart n b hb1 hb2).parts = {n - b, b} := by
-- proof
  simp only [ofSmallerPart, Nat.Partition.ofSums]
  have hnb_pos : n - b ≠ 0 := by omega
  have hb_pos : b ≠ 0 := by omega
  ext x
  simp only [Multiset.count_filter, Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  split_ifs with h1 h2 h3 h4 <;> simp_all

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_ofSmallerPart_parts_card
-- given
  (n b : ℕ)
  (hb1 : 1 ≤ b)
  (hb2 : 2 * b ≤ n) :
-- imply
  (ofSmallerPart n b hb1 hb2).parts.card = 2 := by
-- proof
  rw [partition_ofSmallerPart_parts]
  simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_smallerPartOf_ofSmallerPart
-- given
  (n b : ℕ)
  (hb1 : 1 ≤ b)
  (hb2 : 2 * b ≤ n) :
-- imply
  smallerPartOf (ofSmallerPart n b hb1 hb2) (ofSmallerPart_parts_card n b hb1 hb2) = b := by
-- proof
  simp only [smallerPartOf, partition_ofSmallerPart_parts]
  rw [partition_fold_min_of_two_multiset_eq _ _ _ (by omega)]
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_two_eq
-- given
  (n : ℕ) :
-- imply
  partsCount 2 n = n / 2 := by
-- proof
  simp only [partsCount]
  -- Establish bijection with Finset.Icc 1 (n/2)
  have h : (Finset.Icc 1 (n / 2)).card = n / 2 := by
    rw [Nat.card_Icc]
    omega
  rw [← h]
  -- Now prove the cardinalities are equal via a bijection
  apply Finset.card_bij (fun p hp => smallerPartOf p (Finset.mem_filter.mp hp).2)
  · -- The image is in Icc 1 (n/2)
    intro p hp
    obtain ⟨hb1, hb2, _⟩ := partition_smallerPartOf_spec p (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_Icc]
    constructor
    · exact hb1
    · exact Nat.le_div_iff_mul_le (by omega) |>.mpr (by linarith)
  · -- Injectivity
    intro p₁ hp₁ p₂ hp₂ heq
    obtain ⟨_, _, hparts₁⟩ := partition_smallerPartOf_spec p₁ (Finset.mem_filter.mp hp₁).2
    obtain ⟨_, _, hparts₂⟩ := partition_smallerPartOf_spec p₂ (Finset.mem_filter.mp hp₂).2
    ext
    simp only [hparts₁, hparts₂, heq]
  · -- Surjectivity
    intro b hb
    simp only [Finset.mem_Icc] at hb
    have hb2 : 2 * b ≤ n := by
      have := hb.2
      omega
    use ofSmallerPart n b hb.1 hb2
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, mem_univ, true_and]
      exact partition_ofSmallerPart_parts_card n b hb.1 hb2
    · exact partition_smallerPartOf_ofSmallerPart n b hb.1 hb2

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_sum_eq
-- given
  (n : ℕ) :
-- imply
  partitionCount n = ∑ k ∈ Finset.range (n + 1), partsCount k n := by
-- proof
  simp only [partitionCount, partsCount]
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : Nat.Partition n => p.parts.card)]
  · simp only [Finset.card_univ]
  · intro p _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (partition_numParts_le p)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_genFun
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R] :
-- imply
  HasProd (fun k => ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j))
    (PowerSeries.mk fun n => (partitionCount n : R)) := by
-- proof
  have h := hasProd_powerSeriesMk_card_restricted R (fun _ => True)
  simp only [ite_true] at h
  convert h using 2
  ext n
  have : (restricted n (fun _ => True)).card = partitionCount n := by
    simp only [restricted, partitionCount]
    rw [Finset.filter_true_of_mem (by simp : ∀ x ∈ (Finset.univ : Finset (Nat.Partition n)), ∀ i ∈ x.parts, True)]
    exact Finset.card_univ
  simp only [this]

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
  convert hasProd_powerSeriesMk_card_restricted R (· ≤ m) using 1
  rfl

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
  have h := hasProd_powerSeriesMk_card_restricted R (· ≤ m)
  rw [← h.tprod_eq]
  -- Convert the finite product to match the infinite product form
  have hprod : ∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j)) =
               ∏ k ∈ range m, (if k + 1 ≤ m then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [mem_range] at hk
    simp only [show k + 1 ≤ m by omega, ite_true]
  rw [hprod]
  symm
  apply tprod_eq_prod
  intro k hk
  simp only [mem_range, not_lt] at hk
  simp only [show ¬(k + 1 ≤ m) by omega, ite_false]

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
  rw [partitionCount_genFun_partsLeq_finprod_eq]
  simp only [coeff_mk]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_genFun_partsIn
  {R} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)] :
-- imply
  HasProd (fun k => if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1)
    (PowerSeries.mk fun n => (partsInCount I n : R)) := by
-- proof
  convert hasProd_powerSeriesMk_card_restricted R (· ∈ I) using 1
  rfl

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsInCount_genFun_eq_tprod
  {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
  (I : Set ℕ) [DecidablePred (· ∈ I)] :
-- imply
  PowerSeries.mk (fun n => (partsInCount I n : R)) =
    ∏' k, if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1 :=
-- proof
  (partition_genFun_partsIn (R := R) I).tprod_eq.symm

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma multipliable_partsIn_genFun
  {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]
  (I : Set ℕ) [DecidablePred (· ∈ I)] :
-- imply
  Multipliable (fun k => if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1) :=
-- proof
  (partition_genFun_partsIn (R := R) I).multipliable

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_oddPartsCount_zero_eq :
-- imply
  oddPartsCount 0 = 1 := by
-- proof
  native_decide

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_distinctPartsCount_zero_eq :
-- imply
  distinctPartsCount 0 = 1 := by
-- proof
  native_decide

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isOddParts_zero
-- given
  (p : Nat.Partition 0) :
-- imply
  p.IsOddParts := by
-- proof
  simp only [IsOddParts, partition_zero_parts]
  intro i hi
  exact (Multiset.notMem_zero i hi).elim

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isDistinctParts_zero
-- given
  (p : Nat.Partition 0) :
-- imply
  p.IsDistinctParts := by
-- proof
  simp only [IsDistinctParts, partition_zero_parts, Multiset.nodup_zero]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isOddParts_iff
  {n : ℕ} (p : Nat.Partition n) :
-- imply
  p.IsOddParts ↔ ∀ i ∈ p.parts, Odd i :=
-- proof
  Iff.rfl

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isDistinctParts_iff
  {n : ℕ} (p : Nat.Partition n) :
-- imply
  p.IsDistinctParts ↔ p.parts.Nodup :=
-- proof
  Iff.rfl

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_isDistinctParts_count_le_one_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.IsDistinctParts ↔ ∀ i, p.parts.count i ≤ 1 := by
-- proof
  simp only [IsDistinctParts, Multiset.nodup_iff_count_le_one]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_mem_odds_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p ∈ odds n ↔ p.IsOddParts := by
-- proof
  simp only [odds, restricted, Finset.mem_filter, mem_univ, true_and, IsOddParts]
  constructor
  · intro h i hi
    exact Nat.not_even_iff_odd.mp (h i hi)
  · intro h i hi
    exact Nat.not_even_iff_odd.mpr (h i hi)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_mem_distincts_iff
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p ∈ distincts n ↔ p.IsDistinctParts := by
-- proof
  simp only [distincts, Finset.mem_filter, mem_univ, true_and, IsDistinctParts]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_oddPartsCount_eq_filter_card
-- given
  (n : ℕ) :
-- imply
  oddPartsCount n = ((Finset.univ : Finset (Nat.Partition n)).filter IsOddParts).card := by
-- proof
  simp only [oddPartsCount]
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (partition_mem_odds_iff p).mp hp
  · intro p₁ _ p₂ _ h
    exact h
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and] at hp
    exact ⟨p, (partition_mem_odds_iff p).mpr hp, rfl⟩

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_distinctPartsCount_eq_filter_card
-- given
  (n : ℕ) :
-- imply
  distinctPartsCount n = ((Finset.univ : Finset (Nat.Partition n)).filter IsDistinctParts).card := by
-- proof
  simp only [distinctPartsCount]
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (partition_mem_distincts_iff p).mp hp
  · intro p₁ _ p₂ _ h
    exact h
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and] at hp
    exact ⟨p, (partition_mem_distincts_iff p).mpr hp, rfl⟩

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_odd_eq_distinct
  (n : ℕ) :
-- imply
  (odds n).card = (distincts n).card :=
-- proof
  card_odds_eq_card_distincts n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_oddPartsCount_eq_distinctPartsCount
  (n : ℕ) :
-- imply
  oddPartsCount n = distinctPartsCount n :=
-- proof
  partition_odd_eq_distinct n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_isOddParts_eq_card_isDistinctParts
-- given
  (n : ℕ) :
-- imply
  ((Finset.univ : Finset (Nat.Partition n)).filter IsOddParts).card =
    ((Finset.univ : Finset (Nat.Partition n)).filter IsDistinctParts).card := by
-- proof
  have h1 : (Finset.univ : Finset (Nat.Partition n)).filter IsOddParts = odds n := by
    ext p
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (partition_mem_odds_iff p).symm
  have h2 : (Finset.univ : Finset (Nat.Partition n)).filter IsDistinctParts = distincts n := by
    ext p
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (partition_mem_distincts_iff p).symm
  rw [h1, h2]
  exact partition_odd_eq_distinct n

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sorted_countP_gt_iff
  {sl : List ℕ}
-- given
  (hsl : sl.Pairwise (· ≥ ·))
  (j : ℕ)
  (hj : j < sl.length)
  (i : ℕ) :
-- imply
  sl.countP (· > i) > j ↔ sl[j] > i := by
-- proof
  -- Helper for sorted lists: earlier elements are larger
  have sorted_ge : ∀ {a b : ℕ} (hab : a ≤ b) (hb : b < sl.length), sl[a]'(Nat.lt_of_le_of_lt hab hb) ≥ sl[b] := by
    intro a b hab hb
    have ha : a < sl.length := Nat.lt_of_le_of_lt hab hb
    by_cases heq : a = b
    · subst heq; rfl
    · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
      rw [List.pairwise_iff_getElem] at hsl
      exact hsl (i := a) (j := b) ha hb hlt
  constructor
  · -- If countP > j, then sl[j] > i
    intro h
    by_contra hle
    push Not at hle
    -- If sl[j] ≤ i, then sl[j], sl[j+1], ... are all ≤ i, so countP ≤ j
    have hcount : sl.countP (· > i) ≤ j := by
      have htake : (sl.take j).countP (· > i) + (sl.drop j).countP (· > i) = sl.countP (· > i) := by
        rw [← List.countP_append, List.take_append_drop]
      have hdrop_zero : (sl.drop j).countP (· > i) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx
        simp only [decide_eq_true_eq, not_lt]
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [List.getElem_drop]
        have hjk : j ≤ j + k := Nat.le_add_right j k
        have hjkl : j + k < sl.length := by rw [List.length_drop] at hk; omega
        have hge : sl[j] ≥ sl[j + k] := sorted_ge hjk hjkl
        omega
      rw [hdrop_zero, add_zero] at htake
      calc sl.countP (· > i) = (sl.take j).countP (· > i) := htake.symm
        _ ≤ (sl.take j).length := List.countP_le_length
        _ ≤ j := List.length_take_le j sl
    omega
  · -- If sl[j] > i, then sl[0], ..., sl[j] are all > i, so countP ≥ j+1 > j
    intro h
    have htake_all : (sl.take (j + 1)).countP (· > i) = j + 1 := by
      have hlen : (sl.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      have hall : ∀ x ∈ sl.take (j + 1), x > i := by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [List.length_take] at hk
        have hkj : k ≤ j := by omega
        rw [List.getElem_take]
        have hkl : k < sl.length := by omega
        have hge : sl[k]'hkl ≥ sl[j] := sorted_ge hkj hj
        omega
      have hfilter_eq : (sl.take (j + 1)).filter (· > i) = sl.take (j + 1) := by
        rw [List.filter_eq_self]; intro x hx; simp only [decide_eq_true_eq]; exact hall x hx
      rw [List.countP_eq_length_filter, hfilter_eq, hlen]
    have htake_le : (sl.take (j + 1)).countP (· > i) ≤ sl.countP (· > i) := by
      have heq : sl.take (j + 1) ++ sl.drop (j + 1) = sl := List.take_append_drop (j + 1) sl
      calc (sl.take (j + 1)).countP (· > i)
        ≤ (sl.take (j + 1)).countP (· > i) + (sl.drop (j + 1)).countP (· > i) := Nat.le_add_right _ _
        _ = (sl.take (j + 1) ++ sl.drop (j + 1)).countP (· > i) := by rw [List.countP_append]
        _ = sl.countP (· > i) := by rw [heq]
    omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_transpose_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.transpose.transpose = p := by
-- proof
  -- We need to show the parts multisets are equal
  apply Nat.Partition.ext_iff.mpr
  -- Use multiset extensionality: show counts are equal for all k
  rw [Multiset.ext]
  intro k
  -- For k = 0, both counts are 0 (partition parts are positive)
  by_cases hk : k = 0
  · subst hk
    have h1 : Multiset.count 0 p.transpose.transpose.parts = 0 := by
      rw [Multiset.count_eq_zero]
      exact fun hm => (p.transpose.transpose.parts_pos hm).ne rfl
    have h2 : Multiset.count 0 p.parts = 0 := by
      rw [Multiset.count_eq_zero]
      exact fun hm => (p.parts_pos hm).ne rfl
    rw [h1, h2]
  · -- For k > 0, the proof uses the Young diagram involution property.
      -- The key insight is that transpose.transpose.parts = p.parts as multisets.
      -- This follows from the bijection property of Young diagrams.
      push Not at hk
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      -- Set up the sorted list representation
      set sl := p.parts.sort (· ≥ ·) with hsl_def
      have hsl_eq : (sl : Multiset ℕ) = p.parts := Multiset.sort_eq p.parts (· ≥ ·)
      have hsl_sorted : sl.Pairwise (· ≥ ·) := Multiset.pairwise_sort p.parts (· ≥ ·)
      -- The key fact: filter card on sorted list equals countP
      have hfilter_countP : ∀ i, (p.parts.filter (· > i)).card = sl.countP (· > i) := by
        intro i
        conv_lhs => rw [← hsl_eq]
        simp only [Multiset.filter_coe, List.countP_eq_length_filter]
        rfl
      -- Key relationship: sl.length = p.parts.card
      have hsl_len : sl.length = p.parts.card := by
        rw [← Multiset.coe_card, hsl_eq]
      -- Handle empty partition case
      by_cases hparts_empty : p.parts = 0
      · -- If p.parts is empty, both counts are 0
        have h1 : Multiset.count k p.transpose.transpose.parts = 0 := by
          rw [Multiset.count_eq_zero]
          intro hm
          have hsum := p.transpose.transpose.parts_sum
          have hn0 : n = 0 := by
            have := p.parts_sum
            rw [hparts_empty] at this
            simp at this
            exact this.symm
          subst hn0
          -- transpose.transpose.parts.sum = 0
          -- But k ∈ transpose.transpose.parts and k > 0, contradiction
          have hpos := p.transpose.transpose.parts_pos hm
          have hle := Multiset.le_sum_of_mem hm
          omega
        have h2 : Multiset.count k p.parts = 0 := by
          rw [hparts_empty]
          simp
        rw [h1, h2]
      · -- Non-empty partition case
        have hsl_ne : sl ≠ [] := by
          intro heq
          have : (sl : Multiset ℕ) = 0 := by simp [heq]
          rw [hsl_eq] at this
          exact hparts_empty this
        have h0 : 0 < sl.length := by
          rw [List.length_pos_iff_ne_nil]
          exact hsl_ne
        -- Helper for sorted lists: earlier elements are larger
        have sorted_ge : ∀ {a b : ℕ} (hab : a ≤ b) (hb : b < sl.length),
            sl[a]'(Nat.lt_of_le_of_lt hab hb) ≥ sl[b] := by
          intro a b hab hb
          have ha : a < sl.length := Nat.lt_of_le_of_lt hab hb
          by_cases heq : a = b
          · subst heq; rfl
          · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
            rw [List.pairwise_iff_getElem] at hsl_sorted
            exact hsl_sorted (i := a) (j := b) ha hb hlt
        -- Use the fact that transpose.transpose.parts = (sl : Multiset ℕ) = p.parts
        rw [← hsl_eq]
        -- Now we need: count k (transpose.transpose.parts) = count k sl
        -- Key helper: count of i with countP (· > i) > j equals sl[j]
        have h_countP_count : ∀ j (hj : j < sl.length),
            (List.range sl[0]).countP (fun i => sl.countP (· > i) > j) = sl[j] := by
          intro j hj
          -- The condition sl.countP (· > i) > j is equivalent to sl[j] > i
          have heq_iff : ∀ i, (sl.countP (· > i) > j) ↔ (i < sl[j]) := by
            intro i
            have h := partition_sorted_countP_gt_iff hsl_sorted j hj i
            omega
          -- Rewrite the countP using the equivalence
          have hcountP_eq : (List.range sl[0]).countP (fun i => sl.countP (· > i) > j) =
                            (List.range sl[0]).countP (fun i => i < sl[j]) := by
            apply List.countP_congr
            intro i _
            simp only [decide_eq_true_eq]
            exact heq_iff i
          rw [hcountP_eq]
          -- Count of i < sl[j] in [0, sl[0]) is min(sl[j], sl[0]) = sl[j]
          have hle : sl[j] ≤ sl[0] := sorted_ge (Nat.zero_le j) hj
          -- The filter [0, sl[0]) ∩ {i : i < sl[j]} = [0, min(sl[j], sl[0])) = [0, sl[j])
          have hcount_lt : (List.range sl[0]).countP (fun i => i < sl[j]) = sl[j] := by
            rw [List.countP_eq_length_filter]
            have hfilter_eq : (List.range sl[0]).filter (fun i => i < sl[j]) = List.range sl[j] := by
              have key : ∀ i, i ∈ (List.range sl[0]).filter (fun i => i < sl[j]) ↔ i ∈ List.range sl[j] := by
                intro i
                simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
                constructor
                · intro ⟨_, hi⟩; exact hi
                · intro hi; exact ⟨Nat.lt_of_lt_of_le hi hle, hi⟩
              have hnodup1 : ((List.range sl[0]).filter (fun i => i < sl[j])).Nodup := by
                apply List.Nodup.filter
                exact List.nodup_range
              have hnodup2 : (List.range sl[j]).Nodup := List.nodup_range
              have hperm : ((List.range sl[0]).filter (fun i => i < sl[j])).Perm (List.range sl[j]) := by
                rw [List.perm_ext_iff_of_nodup hnodup1 hnodup2]
                exact key
              have hsorted1 : ((List.range sl[0]).filter (fun i => i < sl[j])).Pairwise (· < ·) := by
                apply List.Pairwise.filter
                exact List.pairwise_lt_range
              have hsorted2 : (List.range sl[j]).Pairwise (· < ·) := List.pairwise_lt_range
              exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => (Nat.lt_irrefl _ (Nat.lt_trans h1 h2)).elim)
                hsorted1 hsorted2
            rw [hfilter_eq, List.length_range]
          exact hcount_lt
        -- The key insight: both transpose.transpose.parts and sl have the same sum (= n)
        -- and the same "shape" (constructed from the same data via Young diagram transpose)
        have h_sl_pos : ∀ x ∈ sl, 0 < x := by
          intro x hx
          have : x ∈ (sl : Multiset ℕ) := hx
          rw [hsl_eq] at this
          exact p.parts_pos this
        -- Define the intermediate constructions
        let tp_list := (List.range (sl[0]'h0)).map (fun i => sl.countP (· > i))
        let tp : Multiset ℕ := (↑tp_list : Multiset ℕ).filter (· > 0)
        let tp_largest := tp.fold max 0
        let ttp_list := (List.range tp_largest).map (fun j => (tp.filter (· > j)).card)
        let ttp : Multiset ℕ := (↑ttp_list : Multiset ℕ).filter (· > 0)
        -- Key lemma: fold max 0 equals sup for multisets
        have h_fold_max_eq_sup : ∀ (s : Multiset ℕ), s.fold max 0 = s.sup := by
          intro s
          induction s using Multiset.induction with
          | empty => rfl
          | cons a t ih =>
            simp only [Multiset.fold_cons_left, Multiset.sup_cons, ih]
        -- Show that p.parts.fold max 0 = sl[0] (the largest element)
        have h_largest : p.parts.fold max 0 = sl[0]'h0 := by
          rw [h_fold_max_eq_sup, ← hsl_eq]
          -- (↑sl).sup = sl[0] for non-empty sorted decreasing list
          have hsl_ne' : sl ≠ [] := hsl_ne
          obtain ⟨a, as, hsl_eq'⟩ : ∃ a as, sl = a :: as := List.exists_cons_of_ne_nil hsl_ne'
          simp only [hsl_eq', List.getElem_cons_zero]
          rw [show (↑(a :: as) : Multiset ℕ) = a ::ₘ ↑as from rfl, Multiset.sup_cons]
          have h_all_le : ∀ x ∈ as, x ≤ a := by
            intro x hx
            have hsorted' : (a :: as).Pairwise (· ≥ ·) := hsl_eq' ▸ hsl_sorted
            rw [List.pairwise_cons] at hsorted'
            exact hsorted'.1 x hx
          have h_sup_le : (↑as : Multiset ℕ).sup ≤ a := Multiset.sup_le.mpr (fun x hx => h_all_le x hx)
          exact sup_eq_left.mpr h_sup_le
        -- Show that p.transpose.parts = tp
        have h_tp_eq : p.transpose.parts = tp := by
          unfold transpose
          simp only
          rw [h_largest]
          -- Need to show the multisets are equal
          have hmap_eq : (Finset.range (sl[0]'h0)).val.map
              (fun i => (p.parts.filter (· > i)).card) = ↑tp_list := by
            rw [Finset.range_val]
            -- Multiset.range n = ↑(List.range n) by rfl
            show Multiset.map (fun i => (p.parts.filter (· > i)).card) (Multiset.range (sl[0]'h0)) =
                 ↑(tp_list)
            rw [show Multiset.range (sl[0]'h0) = ↑(List.range (sl[0]'h0)) from rfl]
            rw [Multiset.map_coe]
            congr 1
            apply List.map_congr_left
            intro i _
            exact hfilter_countP i
          rw [hmap_eq]
        -- Establish tp_largest = sl.length
        have h_tp_largest : tp_largest = sl.length := by
          show tp.fold max 0 = sl.length
          have h_countP_0 : sl.countP (· > 0) = sl.length := by
            rw [List.countP_eq_length]
            intro x hx
            simp only [decide_eq_true_eq]
            exact h_sl_pos x hx
          have h0_in_range : 0 ∈ List.range (sl[0]'h0) := by
            rw [List.mem_range]
            exact h_sl_pos (sl[0]'h0) (List.getElem_mem h0)
          have h_len_in_tp_list : sl.length ∈ tp_list := by
            rw [List.mem_map]
            exact ⟨0, h0_in_range, h_countP_0⟩
          have h_len_pos : 0 < sl.length := h0
          have h_len_in_tp : sl.length ∈ tp := by
            rw [Multiset.mem_filter]
            exact ⟨h_len_in_tp_list, h_len_pos⟩
          have h_all_le : ∀ x ∈ tp, x ≤ sl.length := by
            intro x hx
            rw [Multiset.mem_filter] at hx
            obtain ⟨hx_mem, _⟩ := hx
            simp only [Multiset.mem_coe] at hx_mem
            rw [List.mem_map] at hx_mem
            obtain ⟨i, _, hi_eq⟩ := hx_mem
            rw [← hi_eq]
            exact List.countP_le_length
          rw [h_fold_max_eq_sup]
          apply le_antisymm
          · exact Multiset.sup_le.mpr h_all_le
          · exact Multiset.le_sup h_len_in_tp
        -- Key: tp.filter (· > j).card = sl[j] for j < sl.length
        have h_filter_card : ∀ j (hj : j < sl.length), (tp.filter (· > j)).card = sl[j] := by
          intro j hj
          have h_filter_eq : tp.filter (· > j) = (↑tp_list : Multiset ℕ).filter (· > j) := by
            conv_lhs => rw [show tp = (↑tp_list : Multiset ℕ).filter (· > 0) from rfl]
            rw [Multiset.filter_filter]
            congr 1
            ext x
            constructor
            · intro ⟨hxj, _⟩; exact hxj
            · intro hxj; exact ⟨hxj, by omega⟩
          rw [h_filter_eq, Multiset.filter_coe, Multiset.coe_card,
              List.countP_eq_length_filter.symm]
          have heq : tp_list.countP (· > j) =
              (List.range (sl[0]'h0)).countP (fun i => sl.countP (· > i) > j) := by
            rw [show tp_list = (List.range (sl[0]'h0)).map (fun i => sl.countP (· > i)) from rfl]
            rw [List.countP_map]
            rfl
          rw [heq]
          exact h_countP_count j hj
        -- Show ttp_list = sl
        have h_ttp_list_eq : ttp_list = sl := by
          conv_lhs =>
            rw [show ttp_list = (List.range tp_largest).map
                (fun j => (tp.filter (· > j)).card) from rfl]
          rw [h_tp_largest]
          apply List.ext_getElem
          · simp [List.length_map, List.length_range]
          · intro i h1 h2
            simp only [List.length_map, List.length_range] at h1
            simp only [List.getElem_map, List.getElem_range]
            exact h_filter_card i h1
        -- Show ttp = ↑sl
        have h_ttp_eq : ttp = ↑sl := by
          conv_lhs => rw [show ttp = (↑ttp_list : Multiset ℕ).filter (· > 0) from rfl]
          rw [h_ttp_list_eq, Multiset.filter_coe]
          have h_filter_sl : sl.filter (· > 0) = sl := by
            rw [List.filter_eq_self]
            intro x hx
            simp only [decide_eq_true_eq]
            exact h_sl_pos x hx
          rw [h_filter_sl]
        -- Show p.transpose.transpose.parts = ttp
        have h_ttp_parts : p.transpose.transpose.parts = ttp := by
          -- Use the fact that p.transpose.parts = tp
          conv_lhs => rw [show p.transpose.transpose = 
              ⟨(Finset.range (p.transpose.parts.fold max 0)).val.map
                (fun i => (p.transpose.parts.filter (· > i)).card) |>.filter (· > 0), 
               p.transpose.transpose.parts_pos, p.transpose.transpose.parts_sum⟩ from rfl]
          simp only
          rw [h_tp_eq]
          rw [Finset.range_val]
          rw [show Multiset.range tp_largest = ↑(List.range tp_largest) from rfl]
          rw [Multiset.map_coe]
        -- Final step: count k in both multisets
        rw [h_ttp_parts, h_ttp_eq]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_size_eq
  {n : ℕ} (p : Nat.Partition n) :
-- imply
  p.transpose.parts.sum = n :=
-- proof
  p.transpose.parts_sum

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_fold_max_le_of_all_le
  (s : Multiset ℕ) (i : ℕ) (h : ∀ x ∈ s, x ≤ i) :
-- imply
  s.fold max 0 ≤ i := by
-- proof
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.fold_cons_left]
    have ha : a ≤ i := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≤ i := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    exact max_le ha (ih hs)

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
  have h : ∃ x ∈ p.parts, x > i := by
    by_contra hc
    push Not at hc
    have hmax : p.parts.fold max 0 ≤ i := partition_fold_max_le_of_all_le p.parts i hc
    omega
  obtain ⟨x, hx_mem, hx_gt⟩ := h
  rw [Multiset.card_pos]
  intro heq
  have : x ∈ p.parts.filter (· > i) := Multiset.mem_filter.mpr ⟨hx_mem, hx_gt⟩
  simp [heq] at this

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_length_eq_largestPart
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.transpose.numParts = p.largestPart := by
-- proof
    unfold transpose numParts largestPart
    simp only
    set largest := p.parts.fold max 0 with h_largest
    set newParts := Multiset.map (fun i => (p.parts.filter (· > i)).card) (range largest).val
    have hall_pos : ∀ x ∈ newParts, x > 0 := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.range_val, Multiset.mem_range] at hi
      exact partition_filter_card_pos_of_lt_largest p i (h_largest ▸ hi)
    have hfilter_eq : newParts.filter (· > 0) = newParts := by
      rw [Multiset.filter_eq_self]
      exact hall_pos
    rw [hfilter_eq]
    rw [Multiset.card_map, Finset.range_val, Multiset.card_range]

  -- Lemma: fold max over a multiset is the sup

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_fold_max_eq_sup
  (s : Multiset ℕ) :
-- imply
  s.fold max 0 = s.sup := by
-- proof
    induction s using Multiset.induction with
    | empty => rfl
    | cons a s ih =>
      simp only [Multiset.fold_cons_left, Multiset.sup_cons, ih]

  -- If all parts are positive and fold max 0 = 0, then the multiset is empty

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_parts_empty_of_fold_max_zero
  {n : ℕ} (p : Nat.Partition n) (h : p.parts.fold max 0 = 0) :
-- imply
  p.parts = 0 := by
-- proof
    rw [partition_fold_max_eq_sup] at h
    by_contra hne
    have hne' : p.parts.card ≠ 0 := fun h => hne (Multiset.card_eq_zero.mp h)
    rw [← Nat.pos_iff_ne_zero] at hne'
    have ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hne'
    have hle : x ≤ p.parts.sup := Multiset.le_sup hx
    have hpos := p.parts_pos hx
    omega

  -- Key lemma: filtering positive elements preserves cardinality for partition parts

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_filter_gt_zero_card_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  (p.parts.filter (· > 0)).card = p.parts.card := by
-- proof
  congr 1
  ext x
  simp only [Multiset.count_filter, gt_iff_lt, Nat.pos_iff_ne_zero, ite_eq_left_iff, not_not]
  intro hx
  subst hx
  rw [eq_comm, Multiset.count_eq_zero]
  exact fun h => (p.parts_pos h).ne rfl

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_transpose_largestPart_eq_length
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.transpose.largestPart = p.numParts := by
-- proof
  unfold transpose largestPart numParts
  simp only
  by_cases hn : p.parts.fold max 0 = 0
  · -- Case: largest part is 0 (empty partition)
    have h_empty := partition_parts_empty_of_fold_max_zero p hn
    simp only [h_empty, Multiset.card_zero]
    rfl
  · -- Case: largest part > 0
    push Not at hn
    have hpos : 0 < p.parts.fold max 0 := Nat.pos_of_ne_zero hn
    have h_first : (p.parts.filter (· > 0)).card = p.parts.card := partition_filter_gt_zero_card_eq p

    set largest := p.parts.fold max 0 with hlarg
    set newParts := (Finset.range largest).val.map
        (fun i => (p.parts.filter (· > i)).card) with hnewParts

    -- The newParts multiset contains p.parts.card at position 0
    have h_mem_card : p.parts.card ∈ newParts := by
      rw [hnewParts, Multiset.mem_map]
      use 0
      constructor
      · exact Multiset.mem_range.mpr hpos
      · exact h_first

    -- All elements are ≤ p.parts.card
    have h_all_le : ∀ x ∈ newParts, x ≤ p.parts.card := by
      intro x hx
      rw [hnewParts, Multiset.mem_map] at hx
      obtain ⟨i, _, hi_eq⟩ := hx
      rw [← hi_eq]
      apply Multiset.card_le_card
      exact Multiset.filter_le (· > i) p.parts

    -- Determine if p.parts.card > 0 or = 0
    have h_card_pos_or_zero : p.parts.card > 0 ∨ p.parts.card = 0 := by omega
    rcases h_card_pos_or_zero with h_card_pos | h_card_zero
    · -- p.parts.card > 0, so it passes the filter
      have h_mem_filtered : p.parts.card ∈ newParts.filter (· > 0) := by
        rw [Multiset.mem_filter]
        exact ⟨h_mem_card, h_card_pos⟩

      -- The max of a set containing p.parts.card where all elements ≤ p.parts.card is p.parts.card
      rw [partition_fold_max_eq_sup]
      apply le_antisymm
      · rw [Multiset.sup_le]
        intro x hx
        rw [Multiset.mem_filter] at hx
        exact h_all_le x hx.1
      · exact Multiset.le_sup h_mem_filtered
    · -- p.parts.card = 0, but then parts is empty, contradicting hpos
      have h_parts_empty : p.parts = 0 := Multiset.card_eq_zero.mp h_card_zero
      rw [h_parts_empty, Multiset.fold_zero] at hlarg
      omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_eq_largestPartCount
-- given
  (n k : ℕ) :
-- imply
  partsCount k n =
    ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.largestPart = k)).card := by
-- proof
  -- Use transpose as a bijection between:
  -- - partitions with k parts
  -- - partitions with largest part k
  apply Finset.card_bij (fun p _ => p.transpose)
  · -- Membership: transpose sends "k parts" to "largest part k"
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [partition_transpose_largestPart_eq_length]
    exact hp
  · -- Injectivity: follows from transpose being an involution
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := congrArg transpose heq
    simp only [partition_transpose_transpose_eq] at h1
    exact h1
  · -- Surjectivity: every partition with largest part k is the transpose of some partition with k parts
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    use q.transpose
    refine ⟨?_, partition_transpose_transpose_eq q⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Need: q.transpose.parts.card = k
    -- We have: q.largestPart = k
    -- By partition_transpose_length_eq_largestPart: q.transpose.numParts = q.largestPart
    have h := partition_transpose_length_eq_largestPart q
    unfold numParts at h
    rw [h, hq]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_sum_eq_largestPartLeq
-- given
  (n k : ℕ) :
-- imply
  ∑ i ∈ Finset.range (k + 1), partsCount i n =
    ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.largestPart ≤ k)).card := by
-- proof
  conv_lhs =>
    congr
    · skip
    · ext i
      rw [partition_partsCount_eq_largestPartCount]
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_range]
  omega

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_partsCount_sum_eq_partsLeqCount
-- given
  (n m : ℕ) :
-- imply
  ∑ k ∈ Finset.range (m + 1), partsCount k n = partsLeqCount m n := by
-- proof
  rw [partition_partsCount_sum_eq_largestPartLeq, partition_filter_largestPart_le_eq_restricted]
  rfl

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
  rw [partitionCount_genFun_partsLeq_finprod_eq]
  ext n
  simp only [coeff_mk]
  have h := partition_partsCount_sum_eq_partsLeqCount n m
  simp only [partsLeqCount] at h
  simp only [← h, Nat.cast_sum]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_multiset_le_fold_max
  {m : Multiset ℕ} :
-- imply
  ∀ x ∈ m, x ≤ m.fold max 0 := by
-- proof
  intro x hx
  induction m using Multiset.induction with
  | empty => simp at hx
  | cons a m' ih =>
    rw [Multiset.mem_cons] at hx
    simp only [Multiset.fold_cons_left]
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_fold_max_mem_of_nonempty
  {m : Multiset ℕ} (h : m ≠ 0) :
-- imply
  m.fold max 0 ∈ m := by
-- proof
  induction m using Multiset.induction with
  | empty => contradiction
  | cons a m' ih =>
    simp only [Multiset.fold_cons_left, Multiset.mem_cons]
    by_cases hm' : m' = 0
    · simp [hm']
    · by_cases ha : a ≥ m'.fold max 0
      · left; exact max_eq_left ha
      · push Not at ha
        right
        rw [max_eq_right (le_of_lt ha)]
        exact ih hm'

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
  intro x hx
  simp only [symToPartsMultiset, Multiset.mem_cons, Multiset.mem_map] at hx
  rcases hx with rfl | ⟨a, _, rfl⟩
  · exact hℓ
  · omega

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
  simp [symToPartsMultiset, Multiset.card_cons, Multiset.card_map]

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
  simp only [symToPartsMultiset, Multiset.fold_cons_left]
  have h : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).fold max 0 ≤ ℓ := by
    induction s.val using Multiset.induction with
    | empty => simp
    | cons a m ih =>
      simp only [Multiset.map_cons, Multiset.fold_cons_left]
      have ha : a.val + 1 ≤ ℓ := by omega
      omega
  omega

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
  simp [symToPartsMultiset, Multiset.erase_cons_head]

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
  simp only [symToPartsMultiset, Multiset.sum_cons, Finset.mem_Icc]
  constructor
  · -- Lower bound: each part is at least 1, so sum of k-1 parts is at least k-1
    have h1 : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).sum ≥ k - 1 := by
      have hcard : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).card = k - 1 := by simp
      have hpos : ∀ x ∈ Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val, 1 ≤ x := by simp
      have := Multiset.card_nsmul_le_sum hpos
      simp only [smul_eq_mul, mul_one, hcard] at this
      exact this
    omega
  · -- Upper bound: each part is at most ℓ
    have h2 : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).sum ≤ (k - 1) * ℓ := by
      have hbound : ∀ x ∈ Multiset.map (fun (x : Fin ℓ) => x.val + 1) (s : Multiset (Fin ℓ)),
          x ≤ ℓ := by
        intro x hx
        simp only [Multiset.mem_map] at hx
        obtain ⟨a, _, rfl⟩ := hx
        omega
      have := Multiset.sum_le_card_nsmul _ _ hbound
      simp only [smul_eq_mul] at this
      calc (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).sum
          ≤ (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).card * ℓ := this
        _ = (k - 1) * ℓ := by simp
    have h3 : ℓ + (k - 1) * ℓ = k * ℓ := by
      cases k with
      | zero => omega
      | succ k' => simp; ring
    omega

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
  -- The proof uses a bijection with Sym (Fin ℓ) (k-1), whose cardinality is
  -- C(ℓ + (k-1) - 1, k-1) = C(k + ℓ - 2, k - 1) by Sym.card_sym_eq_choose.
  --
  -- The bijection maps:
  -- - A partition (ℓ, λ₂, ..., λₖ) to the multiset {λ₂-1, ..., λₖ-1} ⊆ Fin ℓ
  -- - A multiset {a₁, ..., aₖ₋₁} ⊆ Fin ℓ to the partition (ℓ, a₁+1, ..., aₖ₋₁+1) sorted
  --
  -- This is well-defined because:
  -- 1. Each λᵢ ∈ {1, ..., ℓ}, so λᵢ - 1 ∈ {0, ..., ℓ-1} = Fin ℓ
  -- 2. Each aᵢ ∈ Fin ℓ gives aᵢ + 1 ∈ {1, ..., ℓ}
  -- 3. The resulting partition has largest part ℓ (which is explicitly the first part)
  -- 4. The partition has k parts (one ℓ, plus k-1 from the multiset)

  -- Define the sigma type of partitions with k parts and largest ℓ
  let PartsAndLargestSigma := 
    (n : Finset.Icc k (k * ℓ)) × { p : Nat.Partition n // numParts p = k ∧ largestPart p = ℓ }

  -- Step 1: partsAndLargestCountTotal equals the cardinality of this sigma type
  have h_sigma : Fintype.card PartsAndLargestSigma = partsAndLargestCountTotal k ℓ := by
    simp only [PartsAndLargestSigma, partsAndLargestCountTotal, partsAndLargestCount]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_subtype]
    convert Finset.sum_coe_sort (Finset.Icc k (k * ℓ)) _ using 2
    rfl

  -- Step 2: The RHS equals the cardinality of Sym (Fin ℓ) (k-1)
  have h_sym : (k + ℓ - 2).choose (k - 1) = Fintype.card (Sym (Fin ℓ) (k - 1)) := by
    rw [Sym.card_sym_eq_choose, Fintype.card_fin]
    congr 1
    omega

  -- Step 3: Show the two types have the same cardinality via the bijection
  rw [← h_sigma, h_sym]
  apply Fintype.card_congr

  -- The bijection between PartsAndLargestSigma and Sym (Fin ℓ) (k-1):
  -- Forward: Sym (Fin ℓ) (k-1) → PartsAndLargestSigma
  --   s ↦ (⟨n, _⟩, ⟨p, _⟩) where:
  --   - n = ℓ + (s.val.map (·.val + 1)).sum (the partition sum)
  --   - p = Nat.Partition.ofSums n (ℓ ::ₘ s.val.map (·.val + 1))
  --   - numParts p = k (since there's one ℓ plus k-1 parts from s)
  --   - largestPart p = ℓ (since all parts from s are ≤ ℓ)
  --
  -- Backward: PartsAndLargestSigma → Sym (Fin ℓ) (k-1)
  --   (n, p) ↦ (p.parts.erase ℓ).pmap (fun x _ => ⟨x - 1, _⟩)
  --   - Erasing ℓ gives k-1 parts
  --   - Each part x satisfies 1 ≤ x ≤ ℓ, so x - 1 ∈ Fin ℓ
  --
  -- The proof that these are inverses follows from:
  -- - (ℓ ::ₘ m).erase ℓ = m for any multiset m
  -- - For a : Fin ℓ, ⟨(a.val + 1) - 1, _⟩ = a
  -- - The partition sum and numParts/largestPart properties

  -- Define the forward map
  let symToPartitionSum (s : Sym (Fin ℓ) (k - 1)) : ℕ := 
    (symToPartsMultiset ℓ s).sum

  have symToPartitionSum_range (s : Sym (Fin ℓ) (k - 1)) : 
      symToPartitionSum s ∈ Finset.Icc k (k * ℓ) := 
    partition_symToPartsMultiset_sum_range_is k ℓ hk hℓ s

  let symToPartitionParts (s : Sym (Fin ℓ) (k - 1)) : Multiset ℕ := 
    symToPartsMultiset ℓ s

  have symToPartitionParts_sum (s : Sym (Fin ℓ) (k - 1)) : 
      (symToPartitionParts s).sum = symToPartitionSum s := rfl

  let symToPartitionVal (s : Sym (Fin ℓ) (k - 1)) : Nat.Partition (symToPartitionSum s) := 
    Nat.Partition.ofSums _ (symToPartitionParts s) (symToPartitionParts_sum s)

  have symToPartitionVal_parts (s : Sym (Fin ℓ) (k - 1)) : 
      (symToPartitionVal s).parts = symToPartitionParts s := by
    simp only [symToPartitionVal, symToPartitionParts, ofSums_parts]
    ext x
    simp only [Multiset.count_filter, symToPartsMultiset]
    split_ifs with h
    · rfl
    · push Not at h
      subst h
      symm
      rw [Multiset.count_eq_zero]
      intro hx
      have := partition_symToPartsMultiset_pos ℓ hℓ s 0 hx
      omega

  have symToPartitionVal_numParts (s : Sym (Fin ℓ) (k - 1)) : 
      numParts (symToPartitionVal s) = k := by
    simp only [numParts, symToPartitionVal_parts, symToPartitionParts, symToPartsMultiset,
      Multiset.card_cons, Multiset.card_map]
    have := s.prop
    omega

  have symToPartitionVal_largestPart (s : Sym (Fin ℓ) (k - 1)) : 
      largestPart (symToPartitionVal s) = ℓ := by
    simp only [largestPart, symToPartitionVal_parts, symToPartitionParts, symToPartsMultiset,
      Multiset.fold_cons_left]
    have h : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).fold max 0 ≤ ℓ := by
      induction s.val using Multiset.induction with
      | empty => simp
      | cons a m ih =>
        simp only [Multiset.map_cons, Multiset.fold_cons_left]
        have ha : a.val + 1 ≤ ℓ := by omega
        omega
    omega

  -- Define the forward map as a function to PartsAndLargestSigma
  let toSigma (s : Sym (Fin ℓ) (k - 1)) : PartsAndLargestSigma := 
    ⟨⟨symToPartitionSum s, symToPartitionSum_range s⟩, 
     ⟨symToPartitionVal s, symToPartitionVal_numParts s, symToPartitionVal_largestPart s⟩⟩

  -- Helper for HEq handling
  have parts_eq_of_heq : ∀ {n m : ℕ} (h : n = m) 
      {x : { p : Nat.Partition n // numParts p = k ∧ largestPart p = ℓ }} 
      {y : { p : Nat.Partition m // numParts p = k ∧ largestPart p = ℓ }},
      HEq x y → x.val.parts = y.val.parts := by
    intro n m h x y hxy
    subst h
    simp only [heq_eq_eq] at hxy
    rw [hxy]

  -- Prove injectivity
  have toSigma_injective : Function.Injective toSigma := by
    intro s t hst
    -- Extract the equality of first components and HEq of second components
    have hn : symToPartitionSum s = symToPartitionSum t := by
      have := congrArg (fun x => x.1.val) hst
      exact this
    have hp : HEq (toSigma s).2 (toSigma t).2 := Sigma.mk.inj hst |>.2
    -- From hn, we get that the multiset sums are equal
    have hsum : (symToPartsMultiset ℓ s).sum = (symToPartsMultiset ℓ t).sum := hn
    -- Use hn to convert hp from HEq to Eq
    have hmultiset : s.val.map (fun x => x.val + 1) = t.val.map (fun x => x.val + 1) := by
      have hparts : (symToPartitionVal s).parts = (symToPartitionVal t).parts := 
        parts_eq_of_heq hn hp
      rw [symToPartitionVal_parts, symToPartitionVal_parts] at hparts
      simp only [symToPartitionParts, symToPartsMultiset, Multiset.cons_inj_right] at hparts
      exact hparts
    -- The map x ↦ x.val + 1 is injective on Fin ℓ
    ext a
    have : s.val.count a = t.val.count a := by
      have := congrArg (Multiset.count (a.val + 1)) hmultiset
      simp only [Multiset.count_map_eq_count' (fun x : Fin ℓ => x.val + 1) _ 
        (fun x y h => by simp only [add_left_inj] at h; exact Fin.ext h)] at this
      exact this
    exact this

  -- Since both types are finite and toSigma is injective, 
  -- we can construct an equivalence by showing toSigma is surjective.
  -- We prove surjectivity by constructing an explicit right inverse.

  -- Helper lemmas for the backward map
  have fold_max_mem : ∀ (m : Multiset ℕ), m ≠ 0 → m.fold max 0 ∈ m := by
    intro m hm
    induction m using Multiset.induction with
    | empty => simp at hm
    | cons a m ih =>
      simp only [Multiset.fold_cons_left]
      by_cases hm' : m = 0
      · simp [hm']
      · by_cases ha : a ≥ m.fold max 0
        · simp [max_eq_left ha]
        · push Not at ha
          simp only [max_eq_right (le_of_lt ha)]
          exact Multiset.mem_cons_of_mem (ih hm')

  have le_fold_max : ∀ (m : Multiset ℕ) (x : ℕ), x ∈ m → x ≤ m.fold max 0 := by
    intro m x hx
    induction m using Multiset.induction with
    | empty => simp at hx
    | cons a m ih =>
      simp only [Multiset.mem_cons] at hx
      simp only [Multiset.fold_cons_left]
      obtain rfl | hx := hx
      · exact le_max_left x (m.fold max 0)
      · exact le_trans (ih hx) (le_max_right a (m.fold max 0))

  -- Define the backward map
  let fromSigma (x : PartsAndLargestSigma) : Sym (Fin ℓ) (k - 1) := by
    obtain ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩ := x
    -- p.parts has k parts, largest is ℓ
    -- After erasing ℓ, we have k-1 parts, each in {1, ..., ℓ}
    have hp_card : p.parts.card = k := hp_numParts
    have hp_max : p.parts.fold max 0 = ℓ := hp_largestPart
    have h_nonempty : p.parts ≠ 0 := by
      simp only [← Multiset.card_pos, hp_card]
      omega
    have h_ell_mem : ℓ ∈ p.parts := by
      have := fold_max_mem p.parts h_nonempty
      simp only [hp_max] at this
      exact this
    let erased := p.parts.erase ℓ
    have h_erased_card : erased.card = k - 1 := by
      simp only [erased, Multiset.card_erase_of_mem h_ell_mem, hp_card]
      rfl
    have h_erased_bound : ∀ y ∈ erased, 1 ≤ y ∧ y ≤ ℓ := by
      intro y hy
      have hy_mem : y ∈ p.parts := Multiset.mem_of_mem_erase hy
      constructor
      · exact p.parts_pos hy_mem
      · have := le_fold_max p.parts y hy_mem
        simp only [hp_max] at this
        exact this
    exact ⟨erased.pmap (fun y hy => ⟨y - 1, by have := h_erased_bound y hy; omega⟩) 
           (fun y hy => hy), by simp [Multiset.card_pmap, h_erased_card]⟩

  -- Prove that fromSigma is a right inverse of toSigma (i.e., toSigma ∘ fromSigma = id)
  -- This makes toSigma surjective
  -- 
  -- The proof outline:
  -- 1. For any x = ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩ ∈ PartsAndLargestSigma
  -- 2. fromSigma x constructs a Sym by erasing ℓ from p.parts and mapping y ↦ y-1
  -- 3. toSigma (fromSigma x) constructs a partition with parts ℓ ::ₘ (map (·+1) ...)
  -- 4. The key is that map (·+1) ∘ map (·-1) = id on positive integers
  -- 5. So the parts are ℓ ::ₘ (p.parts.erase ℓ) = p.parts (by Multiset.cons_erase)
  -- 6. Therefore the sum and partition match
  have toSigma_surj : Function.Surjective toSigma := by
    intro x
    use fromSigma x
    -- The round-trip proof requires showing that:
    -- 1. The sum (symToPartitionSum (fromSigma x)) equals n
    -- 2. The partition (symToPartitionVal (fromSigma x)) equals p
    -- Both follow from: map (·+1) ∘ pmap (·-1) = id on positive integers
    -- and Multiset.cons_erase: ℓ ::ₘ (p.parts.erase ℓ) = p.parts

    -- Extract components of x
    obtain ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩ := x

    -- Establish key properties of p
    have hp_card : p.parts.card = k := hp_numParts
    have hp_max : p.parts.fold max 0 = ℓ := hp_largestPart
    have h_nonempty : p.parts ≠ 0 := by
      simp only [← Multiset.card_pos, hp_card]
      omega
    have h_ell_mem : ℓ ∈ p.parts := by
      have := fold_max_mem p.parts h_nonempty
      simp only [hp_max] at this
      exact this
    have h_erased_bound : ∀ y ∈ p.parts.erase ℓ, 1 ≤ y ∧ y ≤ ℓ := by
      intro y hy
      have hy_mem : y ∈ p.parts := Multiset.mem_of_mem_erase hy
      constructor
      · exact p.parts_pos hy_mem
      · have := le_fold_max p.parts y hy_mem
        simp only [hp_max] at this
        exact this

    -- Key lemma: pmap (·-1) followed by map (·+1) is identity
    have pmap_map_id : ∀ (m : Multiset ℕ) (hm : ∀ y ∈ m, 1 ≤ y ∧ y ≤ ℓ),
        (m.pmap (fun y (hy : y ∈ m) => (⟨y - 1, by have := hm y hy; omega⟩ : Fin ℓ)) 
         (fun y hy => hy)).map (fun x => x.val + 1) = m := by
      intro m hm
      rw [Multiset.map_pmap]
      have eq1 : m.pmap (fun y (hy : y ∈ m) => 
          (⟨y - 1, by have := hm y hy; omega⟩ : Fin ℓ).val + 1) 
          (fun y hy => hy) = 
          m.pmap (fun y _ => y) (fun y hy => hy) := by
        apply Multiset.pmap_congr m
        intro y hy
        have hbound := hm y hy
        have : (⟨y - 1, by have := hm y hy; omega⟩ : Fin ℓ).val = y - 1 := rfl
        omega
      rw [eq1]
      rw [Multiset.pmap_eq_map_attach]
      simp

    -- Show that symToPartsMultiset of fromSigma x equals p.parts
    have h_parts_eq : symToPartsMultiset ℓ (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩) = 
        p.parts := by
      simp only [fromSigma, symToPartsMultiset]
      rw [pmap_map_id (p.parts.erase ℓ) h_erased_bound]
      exact Multiset.cons_erase h_ell_mem

    -- From h_parts_eq, derive the sum equality
    have h_sum_eq : symToPartitionSum (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩) = n := by
      simp only [symToPartitionSum]
      rw [h_parts_eq]
      exact p.parts_sum

    -- Show the sigma type equality
    simp only [toSigma]
    -- We need to show the two sigma elements are equal
    -- First component: ⟨symToPartitionSum (fromSigma x), _⟩ = ⟨n, hn⟩
    -- Second component: ⟨symToPartitionVal (fromSigma x), _, _⟩ = ⟨p, hp_numParts, hp_largestPart⟩

    -- Show the partitions have equal parts
    have h_parts' : (symToPartitionVal (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)).parts = 
        p.parts := by
      rw [symToPartitionVal_parts]
      exact h_parts_eq

    -- First component equality
    have h_first : (⟨symToPartitionSum (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩), 
        symToPartitionSum_range (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)⟩ : 
        Finset.Icc k (k * ℓ)) = ⟨n, hn⟩ := by
      ext
      exact h_sum_eq

    -- Second component HEq - The key facts are established:
    -- 1. h_sum_eq : symToPartitionSum (fromSigma x) = n
    -- 2. h_parts' : the partitions have equal parts
    -- The HEq follows from these by transport, but the dependent type handling is complex.
    -- We use eq_mpr_heq to handle the transport.
    have h_second : HEq 
        (⟨symToPartitionVal (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩), 
          symToPartitionVal_numParts (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩),
          symToPartitionVal_largestPart (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)⟩ : 
         { p : Nat.Partition (symToPartitionSum (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)) // 
           numParts p = k ∧ largestPart p = ℓ })
        (⟨p, hp_numParts, hp_largestPart⟩ : { p : Nat.Partition n // numParts p = k ∧ largestPart p = ℓ }) := by
      -- The key insight: both partitions have the same parts (h_parts'), and the types
      -- are equal (h_sum_eq). We construct the HEq by showing that after transporting
      -- via h_sum_eq, the partitions are equal.
      have h_eq_rec : ∀ (m : ℕ) (hm : m = n) 
          (q : Nat.Partition m) (hq_numParts : numParts q = k) (hq_largestPart : largestPart q = ℓ)
          (hq_parts : q.parts = p.parts),
          HEq (⟨q, hq_numParts, hq_largestPart⟩ : { p : Nat.Partition m // numParts p = k ∧ largestPart p = ℓ })
              (⟨p, hp_numParts, hp_largestPart⟩ : { p : Nat.Partition n // numParts p = k ∧ largestPart p = ℓ }) := by
        intro m hm q hq_numParts hq_largestPart hq_parts
        subst hm
        simp only [heq_eq_eq]
        apply Subtype.ext
        apply Nat.Partition.ext_iff.mpr
        exact hq_parts
      exact h_eq_rec _ h_sum_eq _ 
        (symToPartitionVal_numParts (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩))
        (symToPartitionVal_largestPart (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩))
        h_parts'

    -- Combine using Sigma.ext_iff
    rw [Sigma.ext_iff]
    exact ⟨h_first, h_second⟩

  exact (Equiv.ofBijective toSigma ⟨toSigma_injective, toSigma_surj⟩).symm

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_P_eq
-- given
  (n : ℕ) :
-- imply
  coeff n P = partitionCount n := by
-- proof
  simp only [P, coeff_genFun, partitionCount]
  conv_lhs =>
    arg 2
    ext p
    rw [show p.parts.toFinsupp.prod (fun _ _ => (1 : ℤ)) = 1 by simp [Finsupp.prod]]
  rw [sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_S_eq
-- given
  (n : ℕ) :
-- imply
  coeff n S = if n = 0 then 0 else divisorSum n := by
-- proof
  simp only [S, coeff_mk]
  split_ifs <;> simp

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_X_mul_derivative_P_eq
-- given
  (n : ℕ) :
-- imply
  coeff n (X * derivative P) = n * coeff n P := by
-- proof
  rcases n with _ | n
  · simp [coeff_zero_eq_constantCoeff_apply]
  · rw [coeff_succ_X_mul, coeff_derivative]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_coeff_S_mul_P_eq
-- given
  (n : ℕ) :
-- imply
  coeff n (S * P) = ∑ k ∈ Finset.range n, divisorSum (k + 1) * partitionCount (n - k - 1) := by
-- proof
  rw [coeff_mul]
  simp only [partition_coeff_S_eq, partition_coeff_P_eq]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [sum_range_succ']
  simp only [ite_true, CharP.cast_eq_zero, zero_mul]
  simp only [Nat.succ_ne_zero, ite_false, add_zero]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.sub_sub]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_multiset_sum_sub_eq
  {s t : Multiset ℕ} (h : t ≤ s) :
-- imply
  (s - t).sum = s.sum - t.sum := by
-- proof
  have hadd : s = (s - t) + t := (Multiset.sub_add_cancel h).symm
  calc (s - t).sum = (s - t).sum + t.sum - t.sum := by omega
    _ = ((s - t) + t).sum - t.sum := by rw [Multiset.sum_add]
    _ = s.sum - t.sum := by rw [← hadd]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_replicate_le_of_count_ge
  {s : Multiset ℕ} {a : ℕ} {j : ℕ} (h : j ≤ s.count a) :
-- imply
  Multiset.replicate j a ≤ s := by
-- proof
  rw [Multiset.le_iff_count]
  intro b
  rw [Multiset.count_replicate]
  split_ifs with hba
  · subst hba; exact h
  · exact Nat.zero_le _

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_parts_as_weighted_count_eq
  {n : ℕ}
-- given
  (p : Nat.Partition n) :
-- imply
  p.parts.sum = (p.parts.toFinset).sum (fun d => d * p.parts.count d) := by
-- proof
  induction p.parts using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.toFinset_cons]
    by_cases ha : a ∈ s.toFinset
    · rw [Finset.insert_eq_of_mem ha, ih]
      have key : ∀ x ∈ s.toFinset, x * Multiset.count x s + (if x = a then x else 0) =
             x * Multiset.count x (a ::ₘ s) := by
        intro x _
        rw [Multiset.count_cons]
        split_ifs with hxa <;> ring
      trans (∑ x ∈ s.toFinset, (x * Multiset.count x s + if x = a then x else 0))
      · rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', ha, ↓reduceIte]
        ring
      · exact Finset.sum_congr rfl key
    · simp only [Multiset.mem_toFinset] at ha
      have hcount : s.count a = 0 := Multiset.count_eq_zero.mpr ha
      rw [Finset.sum_insert (by simp [ha]), Multiset.count_cons_self, hcount, ih]
      ring_nf
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ (Multiset.mem_toFinset.mp hx))
      simp [Multiset.count_cons_of_ne hxa]

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
  simp only [parts_sum, Finset.sum_const, smul_eq_mul, mul_comm]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_sum_eq_sum_card_filter_ge
  {α : Type*} (s : Finset α) (f : α → ℕ) (bound : ℕ) (hbound : ∀ a ∈ s, f a ≤ bound) :
-- imply
  s.sum f = (Finset.range bound).sum (fun j => (s.filter (fun a => f a ≥ j + 1)).card) := by
-- proof
  -- Each f(a) = card {j ∈ range (f a)} = card {j ∈ range bound | j < f a}
  have h1 : s.sum f = s.sum (fun a => ((Finset.range bound).filter (fun j => j < f a)).card) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hfa : f a ≤ bound := hbound a ha
    have : (Finset.range bound).filter (fun j => j < f a) = Finset.range (f a) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro ⟨_, hj⟩; exact hj
      · intro hj; exact ⟨Nat.lt_of_lt_of_le hj hfa, hj⟩
    rw [this, Finset.card_range]
  rw [h1]
  -- Use sigma types to swap the order of summation
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  -- Show the two sigma sets have the same cardinality via bijection
  apply Finset.card_bij (fun (p : (a : α) × ℕ) _ => ⟨p.2, p.1⟩)
  · -- Image is in the RHS sigma
    intro ⟨a, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hp ⊢
    obtain ⟨ha, hj_range, hj_lt⟩ := hp
    exact ⟨hj_range, ha, Nat.lt_iff_add_one_le.mp hj_lt⟩
  · -- Injectivity
    intro ⟨a₁, j₁⟩ _ ⟨a₂, j₂⟩ _ heq
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    obtain ⟨hj, ha⟩ := heq
    simp only [Sigma.mk.inj_iff, heq_eq_eq]
    exact ⟨ha, hj⟩
  · -- Surjectivity
    intro ⟨j, a⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hj_range, ha, hge⟩ := hp
    refine ⟨⟨a, j⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range]
    exact ⟨ha, hj_range, Nat.lt_of_succ_le hge⟩

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_count_le_of_partition
  (n d : ℕ) (p : Nat.Partition n) :
-- imply
  p.parts.count d ≤ n := by
-- proof
  by_cases hd : d = 0
  · -- d = 0 case: 0 cannot be in parts of a partition
    have h0 : 0 ∉ p.parts := fun h => Nat.lt_irrefl 0 (p.parts_pos h)
    rw [hd, Multiset.count_eq_zero.mpr h0]
    exact Nat.zero_le n
  · -- d > 0 case
    have h := p.parts_sum
    have hpos : 0 < d := Nat.pos_of_ne_zero hd
    have hrep : Multiset.replicate (p.parts.count d) d ≤ p.parts :=
      Multiset.le_count_iff_replicate_le.mp le_rfl
    have hle : p.parts.count d * d ≤ p.parts.sum := by
      have hsum_rep : (Multiset.replicate (p.parts.count d) d).sum = p.parts.count d * d := by
        simp [Multiset.sum_replicate]
      rw [← hsum_rep]
      obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hrep
      calc (Multiset.replicate (p.parts.count d) d).sum
          ≤ (Multiset.replicate (p.parts.count d) d).sum + u.sum := Nat.le_add_right _ _
        _ = p.parts.sum := by rw [← Multiset.sum_add, ← hu]
    calc p.parts.count d ≤ p.parts.count d * d := Nat.le_mul_of_pos_right _ hpos
      _ ≤ p.parts.sum := hle
      _ = n := h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_count_le_div_of_partition
-- given
  (n d : ℕ)
  (p : Nat.Partition n)
  (hd : 0 < d) :
-- imply
  p.parts.count d ≤ n / d := by
-- proof
  have h1 : Multiset.replicate (p.parts.count d) d ≤ p.parts :=
    Multiset.le_count_iff_replicate_le.mp le_rfl
  have h2 : (Multiset.replicate (p.parts.count d) d).sum ≤ p.parts.sum := by
    obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp h1
    calc (Multiset.replicate (p.parts.count d) d).sum
        ≤ (Multiset.replicate (p.parts.count d) d).sum + u.sum := Nat.le_add_right _ _
      _ = (Multiset.replicate (p.parts.count d) d + u).sum := (Multiset.sum_add _ _).symm
      _ = p.parts.sum := by rw [← hu]
  simp only [Multiset.sum_replicate] at h2
  rw [p.parts_sum] at h2
  exact Nat.le_div_iff_mul_le hd |>.mpr h2

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
  apply partition_sum_eq_sum_card_filter_ge
  intro p _
  exact Nat.le_succ_of_le (partition_count_le_of_partition n d p)

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_card_count_ge_eq_restricted
-- given
  (I : Set ℕ) [DecidablePred (· ∈ I)]
  (hI : ∀ i ∈ I, i > 0)
  (n d j : ℕ)
  (hd : d ∈ I)
  (hdj : d * j ≤ n) :
-- imply
  ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j)).card =
    (restricted (n - d * j) (· ∈ I)).card := by
-- proof
  -- We establish a bijection between the two sets
  apply Finset.card_bij
    -- Forward map: remove j copies of d
    (fun p hp => by
      have hmem : p ∈ restricted n (· ∈ I) := Finset.mem_filter.mp hp |>.1
      have hge : p.parts.count d ≥ j := Finset.mem_filter.mp hp |>.2
      exact removePartCopies p d j (hI d hd) hge)
  · -- The image is in restricted (n - d*j) I
    intro p hp
    simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    have hmem : p ∈ restricted n (· ∈ I) := Finset.mem_filter.mp hp |>.1
    simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hx_orig : x ∈ p.parts := by
      simp only [removePartCopies] at hx
      exact Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    exact hmem x hx_orig
  · -- Injectivity
    intro p₁ hp₁ p₂ hp₂ heq
    have hge₁ : p₁.parts.count d ≥ j := Finset.mem_filter.mp hp₁ |>.2
    have hge₂ : p₂.parts.count d ≥ j := Finset.mem_filter.mp hp₂ |>.2
    simp only [removePartCopies] at heq
    apply Nat.Partition.ext_iff.mpr
    have h : p₁.parts - Multiset.replicate j d = p₂.parts - Multiset.replicate j d := by
      injection heq
    have hle₁ : Multiset.replicate j d ≤ p₁.parts := partition_replicate_le_of_count_ge hge₁
    have hle₂ : Multiset.replicate j d ≤ p₂.parts := partition_replicate_le_of_count_ge hge₂
    calc p₁.parts = (p₁.parts - Multiset.replicate j d) + Multiset.replicate j d :=
           (Multiset.sub_add_cancel hle₁).symm
      _ = (p₂.parts - Multiset.replicate j d) + Multiset.replicate j d := by rw [h]
      _ = p₂.parts := Multiset.sub_add_cancel hle₂
  · -- Surjectivity
    intro q hq
    simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    -- Construct p by adding j copies of d
    have hd_pos : d > 0 := hI d hd
    let p := addPartCopies q d j hd_pos
    have hp_parts_in_I : ∀ x ∈ p.parts, x ∈ I := by
      intro x hx
      simp only [addPartCopies, p] at hx
      simp only [Multiset.mem_add] at hx
      rcases hx with hx_q | hx_rep
      · exact hq x hx_q
      · simp only [Multiset.mem_replicate] at hx_rep
        rcases hx_rep with ⟨_, rfl⟩
        exact hd
    have hp_sum : p.parts.sum = (n - d * j) + d * j := p.parts_sum
    have hp_sum' : p.parts.sum = n := by omega
    -- Cast p to Nat.Partition n
    let p' : Nat.Partition n := ⟨p.parts, @parts_pos _ p, hp_sum'⟩
    use p'
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, restricted, Finset.mem_univ, true_and]
      refine ⟨hp_parts_in_I, ?_⟩
      -- Show count(d, p') ≥ j
      simp only [p', addPartCopies, p]
      rw [Multiset.count_add, Multiset.count_replicate_self]
      omega
    · -- Show removePartCopies p' d j = q
      apply Nat.Partition.ext_iff.mpr
      simp only [removePartCopies, p', addPartCopies, p]
      rw [Multiset.add_sub_cancel_right]

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
  -- The proof establishes a bijection between index pairs:
  -- LHS: (k, d) with k ∈ [0, n-1], d | k+1, d ∈ I
  -- RHS: (d, j) with d ∈ I ∩ [1, n], j ∈ [1, n/d]
  -- via k = d*j - 1, j = (k+1)/d
  --
  -- Key observations:
  -- 1. If d | k+1, then (k+1)/d ≥ 1 (since d ≤ k+1)
  -- 2. If d | k+1 and k < n, then (k+1)/d ≤ n/d
  -- 3. If j ∈ [1, n/d], then d*j - 1 < n (since d*j ≤ d*(n/d) ≤ n)
  -- 4. d | (d*j - 1 + 1) = d*j is automatic
  rw [Finset.sum_sigma']
  conv_rhs =>
    arg 2
    ext d
    rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  -- Forward map: (k, d) ↦ (d, (k+1)/d)
  let i : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun ⟨k, d⟩ => ⟨d, (k + 1) / d⟩
  -- Backward map: (d, j) ↦ (d*j - 1, d)
  let j : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun ⟨d, j⟩ => ⟨d * j - 1, d⟩
  -- Use sum_nbij' with these maps
  apply Finset.sum_nbij' i j
  · -- i maps S to T
    intro ⟨k, d⟩ hkd
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors] at hkd
    obtain ⟨hk, ⟨hdiv, _⟩, hI⟩ := hkd
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, i]
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (Nat.succ_pos k)
    refine ⟨⟨⟨hd_pos, ?_⟩, hI⟩, ⟨?_, ?_⟩⟩
    · -- d ≤ n: since d | k+1 and k < n, we have d ≤ k+1 ≤ n
      calc d ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdiv
           _ ≤ n := hk
    · -- (k+1)/d ≥ 1: since d | k+1 and k+1 ≠ 0
      exact Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos k) hdiv) hd_pos
    · -- (k+1)/d ≤ n/d: since k+1 ≤ n
      exact Nat.div_le_div_right hk
  · -- j maps T to S
    intro ⟨d, jval⟩ hdj
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hdj
    obtain ⟨⟨⟨hd1, hdn⟩, hI⟩, hj1, hjn⟩ := hdj
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors, j]
    have h1 : 1 ≤ d * jval := one_le_mul_of_one_le_of_one_le hd1 hj1
    refine ⟨?_, ⟨?_, ?_⟩, hI⟩
    · -- d * jval - 1 < n
      have h2 : d * jval ≤ n := calc
        d * jval ≤ d * (n / d) := Nat.mul_le_mul_left d hjn
        _ ≤ n := Nat.mul_div_le n d
      omega
    · -- d | (d * jval - 1 + 1) = d * jval
      simp only [Nat.sub_add_cancel h1]
      exact Nat.dvd_mul_right d jval
    · -- d * jval - 1 + 1 ≠ 0
      simp only [Nat.sub_add_cancel h1]
      exact (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hd1)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hj1)).ne'
  · -- j ∘ i = id on S
    intro ⟨k, d⟩ hkd
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors] at hkd
    obtain ⟨_, ⟨hdiv, _⟩, _⟩ := hkd
    simp only [i, j]
    -- Need: ⟨d * ((k+1)/d) - 1, d⟩ = ⟨k, d⟩
    -- This requires d * ((k+1)/d) = k + 1, which holds since d | k+1
    congr 1
    rw [Nat.mul_div_cancel' hdiv]
    omega
  · -- i ∘ j = id on T
    intro ⟨d, jval⟩ hdj
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hdj
    obtain ⟨⟨⟨hd1, _⟩, _⟩, hj1, _⟩ := hdj
    simp only [i, j]
    -- Need: ⟨d, (d*jval - 1 + 1)/d⟩ = ⟨d, jval⟩
    -- This requires (d*jval)/d = jval
    congr 1
    have h1 : 1 ≤ d * jval := one_le_mul_of_one_le_of_one_le hd1 hj1
    simp only [Nat.sub_add_cancel h1]
    exact Nat.mul_div_cancel_left jval (Nat.lt_of_lt_of_le Nat.zero_lt_one hd1)
  · -- f values match: d * f(n - k - 1) = d * f(n - d * ((k+1)/d))
    intro ⟨k, d⟩ hkd
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors] at hkd
    obtain ⟨_, ⟨hdiv, _⟩, _⟩ := hkd
    simp only [i]
    -- Need: d * f(n - k - 1) = d * f(n - d * ((k+1)/d))
    -- Since d | k+1, we have d * ((k+1)/d) = k+1, so n - d * ((k+1)/d) = n - k - 1
    congr 2
    rw [Nat.mul_div_cancel' hdiv]
    omega

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
  /-
  The proof uses a double counting argument. Both sides count weighted pairs.

  **LHS Analysis:**
  n * |restricted n I| = ∑_{p ∈ restricted n I} p.parts.sum  (since each partition sums to n)
  = ∑_{p ∈ restricted n I} ∑_{d ∈ p.parts.toFinset} d * count(d, p)
  = ∑_{d ∈ I, d ≤ n} d * ∑_{p ∈ restricted n I} count(d, p)  (swapping sums)
  = ∑_{d ∈ I, d ≤ n} d * ∑_{j=1}^{⌊n/d⌋} |restricted (n - d·j) I|

  The last step uses: ∑_p count(d, p) = ∑_{j≥1} |{p : count(d,p) ≥ j}|
  and the bijection: {p : count(d,p) ≥ j} ↔ restricted (n - d·j) I
  (removing j copies of d from p gives a partition of n - d·j with parts in I)

  **RHS Analysis:**
  ∑_{k=0}^{n-1} σ_I(k+1) · |restricted (n-k-1) I|
  = ∑_{k=0}^{n-1} (∑_{d | k+1, d ∈ I} d) · |restricted (n-k-1) I|
  = ∑_{k=0}^{n-1} ∑_{d | k+1, d ∈ I} d · |restricted (n-k-1) I|  (distributing)

  Now swap: if d | k+1, write k+1 = d·j for some j ≥ 1, so k = d·j - 1
  and n - k - 1 = n - d·j. The constraint 0 ≤ k < n becomes 1 ≤ d·j ≤ n.

  = ∑_{d ∈ I, d ≤ n} d · ∑_{j=1}^{⌊n/d⌋} |restricted (n - d·j) I|

  **Conclusion:** LHS = RHS since both equal the same expression.
  -/
  -- Rewrite LHS using partition_lhs_eq_sum_parts
  rw [partition_lhs_eq_sum_parts]
  -- Rewrite each p.parts.sum using partition_sum_parts_as_weighted_count_eq
  conv_lhs => arg 2; ext p; rw [partition_sum_parts_as_weighted_count_eq]
  -- Step 1: Extend inner sum from p.parts.toFinset to (Icc 1 n).filter (· ∈ I)
  -- For d ∉ p.parts.toFinset, count(d, p) = 0, so the term is 0
  have h_extend : (restricted n (· ∈ I)).sum (fun p => p.parts.toFinset.sum (fun d => d * p.parts.count d)) =
      (restricted n (· ∈ I)).sum (fun p => ((Finset.Icc 1 n).filter (· ∈ I)).sum (fun d => d * p.parts.count d)) := by
    apply Finset.sum_congr rfl
    intro p hp
    -- p.parts.toFinset ⊆ (Icc 1 n).filter (· ∈ I)
    have hsubset : p.parts.toFinset ⊆ (Finset.Icc 1 n).filter (· ∈ I) := by
      intro d hd
      simp only [Multiset.mem_toFinset] at hd
      simp only [Finset.mem_filter, Finset.mem_Icc]
      simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨⟨p.parts_pos hd, partition_parts_le p d hd⟩, hp d hd⟩
    rw [← Finset.sum_sdiff hsubset]
    have h0 : ((Finset.Icc 1 n).filter (· ∈ I) \ p.parts.toFinset).sum (fun d => d * p.parts.count d) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      simp only [Finset.mem_sdiff, Multiset.mem_toFinset] at hd
      rw [Multiset.count_eq_zero.mpr hd.2, mul_zero]
    rw [h0, zero_add]
  rw [h_extend]
  -- Step 2: Swap the order of summation
  rw [Finset.sum_comm]
  -- Now LHS = ∑_{d ∈ I ∩ [1,n]} (∑_p d * count(d, p))
  --         = ∑_{d ∈ I ∩ [1,n]} d * (∑_p count(d, p))
  conv_lhs =>
    arg 2
    ext d
    rw [← Finset.mul_sum]
  -- Step 3: Use partition_sum_count_eq_sum_card_ge
  -- ∑_p count(d, p) = ∑_{j=0}^{n} |{p : count(d,p) ≥ j+1}|
  conv_lhs =>
    arg 2
    ext d
    rw [partition_sum_count_eq_sum_card_ge]
  -- Now LHS = ∑_{d ∈ I ∩ [1,n]} d * ∑_{j=0}^{n} |{p : count(d,p) ≥ j+1}|
  --
  -- The key insight is that for j+1 > n/d, the filter is empty because
  -- count(d, p) ≤ n/d for any partition p of n (at most n/d copies of d can fit).
  -- So we can restrict the sum to j ∈ [0, n/d - 1], which after shifting becomes j' ∈ [1, n/d].
  --
  -- Then we apply partition_card_count_ge_eq_restricted to convert filter cardinalities to restricted counts.
  -- Finally, we apply partition_divisor_sum_reindex_eq to match the RHS.
  --
  -- The remaining steps are index manipulation and application of the helper lemmas.
  -- All the mathematical content is captured in the helper lemmas; this is bookkeeping.

  -- Step 4: Transform inner sum for each d
  have h_inner : ∀ d ∈ (Finset.Icc 1 n).filter (· ∈ I),
      (Finset.range (n + 1)).sum (fun j =>
        ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card) =
      (Finset.Icc 1 (n / d)).sum (fun j => (restricted (n - d * j) (· ∈ I)).card) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨_, _⟩, hdI⟩ := hd
    have hd_pos : 0 < d := hI d hdI
    -- Step 4a: Truncate sum at n/d (terms for j ≥ n/d are 0)
    have h_trunc : (Finset.range (n + 1)).sum (fun j =>
        ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card) =
        (Finset.range (n / d)).sum (fun j =>
          ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card) := by
      have hsub : Finset.range (n / d) ⊆ Finset.range (n + 1) := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        calc x < n / d := hx
             _ ≤ n := Nat.div_le_self n d
             _ < n + 1 := Nat.lt_succ_self n
      symm
      apply Finset.sum_subset hsub
      intro j hj1 hj2
      simp only [Finset.mem_range, not_lt] at hj1 hj2
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro p _
      simp only [not_le]
      have h : p.parts.count d ≤ n / d := partition_count_le_div_of_partition n d p hd_pos
      omega
    rw [h_trunc]
    -- Step 4b: Shift index from range (n/d) to Icc 1 (n/d)
    have h_shift : Finset.Icc 1 (n / d) = (Finset.range (n / d)).map ⟨(· + 1), Nat.succ_injective⟩ := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro ⟨h1, h2⟩; use x - 1; omega
      · intro ⟨y, hy1, hy2⟩; omega
    rw [h_shift, Finset.sum_map]
    -- Step 4c: Apply partition_card_count_ge_eq_restricted for each term
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Function.Embedding.coeFn_mk]
    have hdj : d * (j + 1) ≤ n := by
      have h1 : j + 1 ≤ n / d := hj
      calc d * (j + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d h1
           _ ≤ n := Nat.mul_div_le n d
    exact partition_card_count_ge_eq_restricted I hI n d (j + 1) hdI hdj
  -- Step 5: Apply the inner transformation
  have h_transform : ((Finset.Icc 1 n).filter (· ∈ I)).sum (fun d =>
      d * (Finset.range (n + 1)).sum (fun j =>
        ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card)) =
      ((Finset.Icc 1 n).filter (· ∈ I)).sum (fun d =>
        d * (Finset.Icc 1 (n / d)).sum (fun j => (restricted (n - d * j) (· ∈ I)).card)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [h_inner d hd]
  rw [h_transform]
  -- Step 6: Apply partition_divisor_sum_reindex_eq in reverse to match RHS
  rw [← partition_divisor_sum_reindex_eq I n (fun m => (restricted m (· ∈ I)).card)]
  -- Step 7: Convert from ∑∑ to (∑) * form
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partitionCount_divisorSum_eq
-- given
  (n : ℕ) :
-- imply
  n * partitionCount n = ∑ k ∈ Finset.range n, divisorSum (k + 1) * partitionCount (n - k - 1) := by
-- proof
  -- Specialize partitionCount_divisorSum_restricted_eq with I = Set.Ioi 0 (positive integers)
  have h := partitionCount_divisorSum_restricted_eq (Set.Ioi 0) (fun i hi => hi) n
  -- Convert restricted to partitionCount:
  -- For partitions, all parts are positive, so restricted n (· > 0) = all partitions
  have h_card : ∀ m, (restricted m (· ∈ Set.Ioi 0)).card = partitionCount m := fun m => by
    simp only [Set.mem_Ioi, restricted, partitionCount]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ i hi => p.parts_pos hi⟩
  simp only [h_card] at h
  -- Convert sum over filtered divisors to divisorSum:
  -- All divisors of k+1 are positive, so the filter is trivial
  have h_sum : ∀ k, ∑ d ∈ (Nat.divisors (k + 1)).filter (· ∈ Set.Ioi 0), d = divisorSum (k + 1) := fun k => by
    have hf : (Nat.divisors (k + 1)).filter (· ∈ Set.Ioi 0) = Nat.divisors (k + 1) := by
      ext d
      simp only [Finset.mem_filter, Set.mem_Ioi, and_iff_left_iff_imp]
      exact Nat.pos_of_mem_divisors
    rw [hf]
    simp [divisorSum, ArithmeticFunction.sigma_one_apply]
  simp only [h_sum] at h
  exact h

/-- [Basics](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Partitions/Basics.lean) -/
@[path]
private lemma partition_X_mul_derivative_P_eq_S_mul_P :
-- imply
  X * derivative P = S * P := by
-- proof
  ext n
  rw [partition_coeff_X_mul_derivative_P_eq, partition_coeff_S_mul_P_eq, partition_coeff_P_eq]
  exact_mod_cast partitionCount_divisorSum_eq n
