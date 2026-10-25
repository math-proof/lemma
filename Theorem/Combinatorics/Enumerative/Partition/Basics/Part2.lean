/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.Basics
open Nat Finset BigOperators PowerSeries
open scoped PowerSeries.WithPiTopology
/-!
# Partition basics

This file formalizes the basic theory of integer partitions from Section
"Partition basics" of the Algebraic Combinatorics textbook.

## Main definitions

* `IversonBracket.iverson` - the Iverson bracket `[P]` converting propositions to 0 or 1
* `FloorCeiling.floor_def` - the floor function `⌊a⌋` (largest integer ≤ a)
* `FloorCeiling.ceil_def` - the ceiling function `⌈a⌉` (smallest integer ≥ a)
* `Nat.Partition.partitionCount` - the partition function `p(n)`, counting partitions of `n`
* `Nat.Partition.partsCount` - the function `p_k(n)`, counting partitions of `n` into `k` parts
* `Nat.Partition.largestPart` - the largest part of a partition (0 for the empty partition)
* `Nat.Partition.transpose` - the conjugate/transpose of a partition
* `Nat.Partition.partsLeqCount` - count of partitions with parts ≤ m
* `Nat.Partition.partsInCount` - count of partitions with parts in a set I

## Main results

### Integer partitions (Definition \ref{def.pars.parts})
* `Nat.Partition.size_eq` - The size of a partition equals the sum of parts (Definition \ref{def.pars.parts} (c))
* `Nat.Partition.parts_pos'` - All parts are positive (Definition \ref{def.pars.parts} (a))
* `Nat.Partition.parts_le` - Each part is bounded by the size
* `Nat.Partition.parts_eq_zero_of_partition_zero` - The partition of 0 has no parts
* `Nat.Partition.parts_card_zero` - The partition of 0 has length 0
* `Nat.Partition.indiscrete_parts_card` - The indiscrete partition (n) has one part
* `Nat.Partition.ofList'` - Construct a partition from a list of positive integers
* `Nat.Partition.eq_iff_parts_eq` - Partitions are determined by their parts

### Iverson bracket (Definition \ref{def.pars.iverson})
* `IversonBracket.iverson` - `[P] = 1` if `P` is true, `[P] = 0` if `P` is false
* `IversonBracket.iverson_true` - `[P] = 1` when `P` is true
* `IversonBracket.iverson_false` - `[P] = 0` when `P` is false
* `IversonBracket.kronecker_eq_iverson` - Kronecker delta `δ_{i,j} = [i = j]`
* `IversonBracket.sum_iverson_eq_card` - `∑ [P(x)] = |{x : P(x)}|`
* `IversonBracket.iverson_and` - `[P ∧ Q] = [P] * [Q]`
* `IversonBracket.iverson_not` - `[¬P] = 1 - [P]`
* `IversonBracket.iverson_or` - `[P ∨ Q] = [P] + [Q] - [P] * [Q]`
* `IversonBracket.iverson_imp` - `[P → Q] = 1 - [P] * (1 - [Q])`

### Floor and ceiling (Definition \ref{def.pars.floor-ceil})
* `FloorCeiling.floor_def` - `n ≤ ⌊a⌋ ↔ n ≤ a` (characterization of floor)
* `FloorCeiling.ceil_def` - `⌈a⌉ ≤ n ↔ a ≤ n` (characterization of ceiling)
* `FloorCeiling.floor_of_int` - `⌊n⌋ = n` for integers
* `FloorCeiling.ceil_of_int` - `⌈n⌉ = n` for integers
* `FloorCeiling.nat_div_eq_floor` - `n / m = ⌊n/m⌋` for natural numbers

### Basic properties (Proposition \ref{prop.pars.basics})
* `Nat.Partition.partsCount_of_gt` - `p_k(n) = 0` when `k > n`
* `Nat.Partition.partsCount_of_gt'` - `@[simp]` lemma for `p_k(n) = 0` when `n < k`
* `Nat.Partition.partsCount_eq_zero_iff` - `p_k(n) = 0` iff `k > n` or `k = 0 ∧ n > 0`
* `Nat.Partition.partsCount_zero` - `p_0(n) = [n = 0]`
* `Nat.Partition.partsCount_one` - `p_1(n) = [n > 0]`
* `Nat.Partition.partsCount_recurrence` - `p_k(n) = p_k(n-k) + p_{k-1}(n-1)` for `k > 0` and `n > 0`
* `Nat.Partition.partsCount_two` - `p_2(n) = ⌊n/2⌋` for `n ∈ ℕ`
* `Nat.Partition.partitionCount_sum` - `p(n) = p_0(n) + p_1(n) + ... + p_n(n)` for `n ∈ ℕ`

### Generating functions (Theorems \ref{thm.pars.main-gf}, \ref{thm.pars.main-gf-parts-n}, \ref{thm.pars.main-gf-parts-I}, \ref{thm.pars.main-gf-0n})
* `Nat.Partition.partitionCount_genFun` - `∑ p(n) x^n = ∏_{k≥1} 1/(1-x^k)`
* `Nat.Partition.partitionCount_genFun_partsLeq` - `∑ p_{parts≤m}(n) x^n = ∏_{k=1}^m 1/(1-x^k)`
* `Nat.Partition.partitionCount_genFun_partsIn` - `∑ p_I(n) x^n = ∏_{k∈I} 1/(1-x^k)`
* `Nat.Partition.partsCountSum_genFun` - `∑ (p_0(n) + ... + p_m(n)) x^n = ∏_{k=1}^m 1/(1-x^k)`

### Odd-distinct theorem (Theorem \ref{thm.pars.odd-dist-equal})
* `Nat.Partition.card_odds_eq_card_distincts` - Euler's odd-distinct identity (from Mathlib)

### Conjugation (Proposition \ref{prop.pars.pkn=dual})
* `Nat.Partition.partsCount_eq_largestPartCount` - `p_k(n) = #{ partitions of n with largest part k }`

### Counting by parts and largest (Proposition \ref{prop.pars.qbinom.intro-count-binom})
* `Nat.Partition.partsAndLargestCountTotal_eq` - `#{ partitions with k parts and largest ℓ } = C(k+ℓ-2, k-1)`

### Partition numbers and divisor sums (Theorem \ref{thm.pars.sigma1})
* `Nat.Partition.partitionCount_divisorSum` - `n·p(n) = ∑_{k=1}^n σ(k)·p(n-k)`

## Implementation notes

We use Mathlib's `Nat.Partition` type which represents a partition as a multiset of positive
integers. This is equivalent to the "weakly decreasing tuple" representation in the source text.

The functions `partsCount` and `partitionCount` are defined as cardinalities of finite sets,
which automatically ensures they are nonnegative. For negative `n`, there are no partitions,
so these functions return 0 naturally.

The generating function theorems use Mathlib's `HasProd` to express convergent infinite products
in the power series topology. The identity `∏_{k≥1} 1/(1-x^k)` is expressed as
`∏_{k≥1} ∑_{j≥0} x^{kj}` since the geometric series `1/(1-x^k) = ∑_{j≥0} x^{kj}`.

## References

* The source text: Algebraic Combinatorics, Section on Partition Basics
* Mathlib: `Mathlib.Combinatorics.Enumerative.Partition.Basic`
* Mathlib: `Mathlib.Combinatorics.Enumerative.Partition.GenFun`
* Mathlib: `Mathlib.Combinatorics.Enumerative.Partition.Glaisher`
-/


/-! ### Iverson bracket notation (Definition \ref{def.pars.iverson})

The **Iverson bracket notation** represents the truth value of a proposition `P`:
- 1 if `P` is true
- 0 if `P` is false

In Lean, this is represented as `if P then 1 else 0` or equivalently `(decide P).toNat`.

The Kronecker delta `δ_{i,j}` is a special case: `δ_{i,j} = [i = j]`.
-/


namespace Nat.Partition

/-! ### Examples from the textbook (Example \ref{exa.pars.pars5})

The partitions of 5 are:
- (5): one part
- (4,1): two parts
- (3,2): two parts
- (3,1,1): three parts
- (2,2,1): three parts
- (2,1,1,1): four parts
- (1,1,1,1,1): five parts
-/


/-- The partition (5) of 5. -/
example : Partition 5 := ⟨{5}, by simp, rfl⟩

/-- The partition (4,1) of 5. -/
example : Partition 5 := ⟨{4, 1}, by simp, rfl⟩

/-- The partition (3,2) of 5. -/
example : Partition 5 := ⟨{3, 2}, by simp, rfl⟩

/-- The partition (3,1,1) of 5. -/
example : Partition 5 := ⟨{3, 1, 1}, by simp, rfl⟩

/-- The partition (2,2,1) of 5. -/
example : Partition 5 := ⟨{2, 2, 1}, by simp, rfl⟩

/-- The partition (2,1,1,1) of 5. -/
example : Partition 5 := ⟨{2, 1, 1, 1}, by simp, rfl⟩

/-- The partition (1,1,1,1,1) of 5. -/
example : Partition 5 := ⟨{1, 1, 1, 1, 1}, by simp, rfl⟩

/-- There are exactly 7 partitions of 5. -/
example : Fintype.card (Partition 5) = 7 := by native_decide

/-! ### Auxiliary lemmas -/

/-- Elements of a multiset are bounded by the fold max. -/
theorem fold_max_ge_of_mem (p : Multiset ℕ) (a : ℕ) (ha : a ∈ p) : a ≤ p.fold max 0 := by
  induction p using Multiset.induction with
  | empty => simp at ha
  | cons b s ih =>
    simp only [Multiset.fold_cons_left]
    simp only [Multiset.mem_cons] at ha
    rcases ha with rfl | ha
    · exact le_max_left a (Multiset.fold max 0 s)
    · exact le_trans (ih ha) (le_max_right b (Multiset.fold max 0 s))

/-- Extending the range of summation when elements are bounded. -/
theorem sum_filter_card_range_extend (s : Multiset ℕ) (M N : ℕ) (hM : ∀ x ∈ s, x ≤ M) (hMN : M ≤ N) :
    (Finset.range N).sum (fun i => (s.filter (· > i)).card) =
    (Finset.range M).sum (fun i => (s.filter (· > i)).card) := by
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

/-- The number of i < M with i < x is exactly min x M. -/
theorem card_range_filter_gt (x M : ℕ) :
    ((Finset.range M).filter (fun i => x > i)).card = min x M := by
  simp only [gt_iff_lt]
  rw [← Finset.card_range (min x M)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Double counting: sum of filter cardinalities equals multiset sum. -/
theorem sum_filter_card_eq_sum (p : Multiset ℕ) (hp : ∀ i ∈ p, 0 < i) :
    (Finset.range (p.fold max 0)).sum (fun i => (p.filter (· > i)).card) = p.sum := by
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
      convert card_range_filter_gt a (max a M) using 2
      simp only [le_max_iff, le_refl, true_or, min_eq_left]
    rw [h1]
    have hbound : ∀ x ∈ s, x ≤ M := fun x hx => fold_max_ge_of_mem s x hx
    have h2 : (Finset.range (max a M)).sum (fun i => (s.filter (· > i)).card) =
              (Finset.range M).sum (fun i => (s.filter (· > i)).card) := by
      apply sum_filter_card_range_extend s M (max a M) hbound (le_max_right a M)
    rw [h2, ih]

/-- Filtering out zeros doesn't change the sum. -/
theorem sum_filter_positive (s : Multiset ℕ) : (s.filter (· > 0)).sum = s.sum := by
  have h := @Multiset.sum_filter_add_sum_filter_not ℕ _ s (· > 0) _
  simp only [gt_iff_lt, Nat.not_lt, Nat.le_zero] at h
  suffices hz : (s.filter (· = 0)).sum = 0 by linarith
  rw [Multiset.sum_eq_zero_iff]
  intro x hx
  simp only [Multiset.mem_filter] at hx
  exact hx.2

end Nat.Partition
