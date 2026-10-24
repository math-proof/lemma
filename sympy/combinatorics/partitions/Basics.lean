/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
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


open Nat Finset BigOperators PowerSeries
open scoped PowerSeries.WithPiTopology
/-! ### Iverson bracket notation (Definition \ref{def.pars.iverson})

The **Iverson bracket notation** represents the truth value of a proposition `P`:
- 1 if `P` is true
- 0 if `P` is false

In Lean, this is represented as `if P then 1 else 0` or equivalently `(decide P).toNat`.

The Kronecker delta `δ_{i,j}` is a special case: `δ_{i,j} = [i = j]`.
-/


namespace IversonBracket

/-- The Iverson bracket converts a proposition to its truth value (0 or 1).
    (Definition \ref{def.pars.iverson})

    This is the standard way to embed boolean values into a semiring:
    - 1 if `P` is true
    - 0 if `P` is false

    In Mathlib, this is `if P then 1 else 0` or `(decide P).toNat` for naturals. -/
abbrev iverson (P : Prop) [Decidable P] {α : Type*} [Zero α] [One α] : α :=
  if P then 1 else 0

/-- Notation `⦃P⦄` for the Iverson bracket. -/
scoped notation "⦃" P "⦄" => iverson P

/-- Example: [2 + 2 = 4] = 1. -/
example : (⦃2 + 2 = 4⦄ : ℕ) = 1 := by simp

/-- Example: [2 + 2 = 5] = 0. -/
example : (⦃2 + 2 = 5⦄ : ℕ) = 0 := by simp

end IversonBracket
/-! ### Floor and ceiling functions (Definition \ref{def.pars.floor-ceil})

The **floor** of a real number `a`, denoted `⌊a⌋`, is the largest integer that is ≤ a.
The **ceiling** of a real number `a`, denoted `⌈a⌉`, is the smallest integer that is ≥ a.

In Mathlib, these are provided by the `FloorRing` and `FloorSemiring` typeclasses:
- `Int.floor` gives the floor as an integer
- `Int.ceil` gives the ceiling as an integer
- `Nat.floor` gives the floor as a natural number (for nonnegative inputs)
- `Nat.ceil` gives the ceiling as a natural number (for nonnegative inputs)

The notation `⌊a⌋` and `⌈a⌉` is available via `import Mathlib`.
-/


namespace FloorCeiling
/-!
## Definition (def.pars.floor-ceil)

Let `a` be a real number.
- `⌊a⌋` (the **floor** of `a`) is the largest integer that is ≤ a.
- `⌈a⌉` (the **ceiling** of `a`) is the smallest integer that is ≥ a.

These are formalized in Mathlib as `Int.floor` and `Int.ceil`.
-/
/-! ### Examples from the textbook

The textbook gives π ≈ 3.14 as an example. We use 3.14 directly as a rational. -/


/-- Example: ⌊3.14⌋ = 3 (approximating ⌊π⌋ = 3). -/
example : ⌊(3.14 : ℚ)⌋ = 3 := by native_decide

/-- Example: ⌈3.14⌉ = 4 (approximating ⌈π⌉ = 4). -/
example : ⌈(3.14 : ℚ)⌉ = 4 := by native_decide

/-- Example: ⌊-3.14⌋ = -4 (approximating ⌊-π⌋ = -4). -/
example : ⌊(-3.14 : ℚ)⌋ = -4 := by native_decide

/-- Example: ⌈-3.14⌉ = -3 (approximating ⌈-π⌉ = -3). -/
example : ⌈(-3.14 : ℚ)⌉ = -3 := by native_decide
/-! ### Connection to natural number division -/
/-! ### Additional properties -/

end FloorCeiling

namespace Nat.Partition
/-! ### Definition of integer partitions (Definition \ref{def.pars.parts})

This section formalizes Definition \ref{def.pars.parts} from the source text.

In Mathlib, `Nat.Partition n` represents partitions of `n`. The underlying data is a
multiset of positive integers that sums to `n`. This is equivalent to the "weakly
decreasing tuple" representation in the source text:

**Definition \ref{def.pars.parts}:**

**(a)** An **(integer) partition** means a (finite) weakly decreasing tuple of positive
integers -- i.e., a finite tuple (λ₁, λ₂, ..., λₘ) of positive integers such that
λ₁ ≥ λ₂ ≥ ... ≥ λₘ.

**(b)** The **parts** of a partition (λ₁, λ₂, ..., λₘ) are simply its entries λ₁, λ₂, ..., λₘ.

**(c)** Let n ∈ ℤ. A **partition of n** means a partition whose size is n.

**(d)** Let n ∈ ℤ and k ∈ ℕ. A **partition of n into k parts** is a partition whose size
is n and whose length is k.

**Implementation note:** Mathlib uses multisets rather than tuples, which is equivalent
since partitions are determined by their parts (with multiplicity), regardless of order.
The "weakly decreasing" constraint in the tuple representation is automatically satisfied
when we sort the multiset in decreasing order.
-/
/-! #### Parts of a partition (Definition \ref{def.pars.parts} (b))

In Mathlib, `Partition.parts` returns the multiset of parts. Each part is a positive
integer (guaranteed by `parts_pos`), and the sum of parts equals the size
(guaranteed by `parts_sum`).

The parts are the fundamental data of a partition. They are positive integers
whose sum equals the size n. We use Mathlib's `Partition.parts` directly rather than
redefining it, and provide wrapper lemmas for the key properties. -/

/-- Constructing a partition from a list of positive integers.
    (Definition \ref{def.pars.parts} (a) - the tuple representation)

    Given a list of positive integers that sums to n, we can construct a partition of n.
    The list need not be sorted; Mathlib's `Partition` uses multisets. -/
def ofList' {n : ℕ} (l : List ℕ) (hl_pos : ∀ i ∈ l, 0 < i) (hl_sum : l.sum = n) : Partition n :=
  ⟨↑l, @fun i hi => hl_pos i (Multiset.mem_coe.mp hi), by simp only [Multiset.sum_coe, hl_sum]⟩
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
/-! ### Partition counting functions -/


/-- The partition function `p(n)`: the number of partitions of `n`.
    (Definition \ref{def.pars.pn-pkn} (b)) -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Partition n)

/-- The function `p_k(n)`: the number of partitions of `n` into exactly `k` parts.
    (Definition \ref{def.pars.pn-pkn} (a)) -/
def partsCount (k n : ℕ) : ℕ :=
  (Finset.univ : Finset (Partition n)).filter (fun p => Multiset.card p.parts = k) |>.card

/-- The number of partitions of `n` with all parts ≤ `m`.
    (Used in Theorem \ref{thm.pars.main-gf-parts-n}) -/
def partsLeqCount (m n : ℕ) : ℕ := (restricted n (· ≤ m)).card

/-- The number of partitions of `n` with all parts in a set `I`.
    (Used in Theorem \ref{thm.pars.main-gf-parts-I}) -/
def partsInCount (I : Set ℕ) [DecidablePred (· ∈ I)] (n : ℕ) : ℕ := (restricted n (· ∈ I)).card
/-! ### Basic API for partition counting functions -/
/-! ### Examples from the textbook

The following examples verify the definitions against the values given in the textbook
following Definition \ref{def.pars.pn-pkn}. -/


/-- Example: `p(5) = 7`. The 7 partitions of 5 are:
    (5), (4,1), (3,2), (3,1,1), (2,2,1), (2,1,1,1), (1,1,1,1,1). -/
example : partitionCount 5 = 7 := by native_decide

/-- Example: `p_0(5) = 0`. There are no partitions of 5 into 0 parts. -/
example : partsCount 0 5 = 0 := by native_decide

/-- Example: `p_1(5) = 1`. The only partition of 5 into 1 part is (5). -/
example : partsCount 1 5 = 1 := by native_decide

/-- Example: `p_2(5) = 2`. The partitions of 5 into 2 parts are (4,1) and (3,2). -/
example : partsCount 2 5 = 2 := by native_decide

/-- Example: `p_3(5) = 2`. The partitions of 5 into 3 parts are (3,1,1) and (2,2,1). -/
example : partsCount 3 5 = 2 := by native_decide

/-- Example: `p_4(5) = 1`. The only partition of 5 into 4 parts is (2,1,1,1). -/
example : partsCount 4 5 = 1 := by native_decide

/-- Example: `p_5(5) = 1`. The only partition of 5 into 5 parts is (1,1,1,1,1). -/
example : partsCount 5 5 = 1 := by native_decide
/-! ### Basic properties of partition numbers -/


/-- The number of parts of a partition equals the cardinality of its parts multiset. -/
def numParts {n : ℕ} (p : Partition n) : ℕ := Multiset.card p.parts

/-- The largest part of a partition (0 for the empty partition).
    (Convention \ref{conv.pars.largest-part-0}) -/
def largestPart {n : ℕ} (p : Partition n) : ℕ :=
  p.parts.fold max 0
/-! ### Helper lemmas for the recurrence relation -/


/-- A partition containing 1 as a part. -/
abbrev containsOne {n : ℕ} (p : Partition n) : Prop := 1 ∈ p.parts

instance {n : ℕ} : DecidablePred (containsOne (n := n)) :=
  fun p => Multiset.decidableMem 1 p.parts

/-- Partitions of n into k parts that contain 1. -/
def partsWithOne (k n : ℕ) : Finset (Partition n) :=
  (Finset.univ : Finset (Partition n)).filter fun p => p.parts.card = k ∧ containsOne p

/-- Partitions of n into k parts that don't contain 1. -/
def partsWithoutOne (k n : ℕ) : Finset (Partition n) :=
  (Finset.univ : Finset (Partition n)).filter fun p => p.parts.card = k ∧ ¬containsOne p

theorem sum_ge_card_of_all_pos {s : Multiset ℕ} (h : ∀ x ∈ s, x > 0) : s.sum ≥ s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha : a > 0 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, x > 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have := ih ht
    omega

theorem sum_map_sub_one_eq {s : Multiset ℕ} (h : ∀ x ∈ s, x > 1) :
    (s.map (· - 1)).sum = s.sum - s.card := by
  have hpos : ∀ x ∈ s, x > 0 := fun x hx => Nat.lt_trans Nat.zero_lt_one (h x hx)
  have hge : s.sum ≥ s.card := sum_ge_card_of_all_pos hpos
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : a > 1 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, x > 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have htpos : ∀ x ∈ t, x > 0 := fun x hx => Nat.lt_trans Nat.zero_lt_one (ht x hx)
    have htge : t.sum ≥ t.card := sum_ge_card_of_all_pos htpos
    rw [ih ht htpos htge]
    omega

/-- Remove one 1 from a partition containing 1 to get a partition of n-1. -/
def removeOne {n : ℕ} (p : Partition n) (h : 1 ∈ p.parts) : Partition (n - 1) :=
  Partition.ofSums (n - 1) (p.parts.erase 1) (by
    have hsum : p.parts.sum = (p.parts.erase 1).sum + 1 := by
      rw [← Multiset.cons_erase h]; simp [add_comm]
    rw [p.parts_sum] at hsum
    omega)

/-- Add one 1 to a partition to get a partition of n+1. -/
def addOne {n : ℕ} (p : Partition n) : Partition (n + 1) :=
  Partition.ofSums (n + 1) (1 ::ₘ p.parts) (by simp [p.parts_sum, add_comm])

/-- Subtract 1 from each part of a partition (when all parts > 1) to get a partition of n - k. -/
def subtractOneFromEach {n k : ℕ} (p : Partition n) (hk : p.parts.card = k)
    (h : ∀ x ∈ p.parts, x > 1) : Partition (n - k) :=
  Partition.ofSums (n - k) (p.parts.map (· - 1)) (by
    rw [sum_map_sub_one_eq h, p.parts_sum, hk])

/-- Add 1 to each part of a partition to get a partition of n + k. -/
def addOneToEach {n k : ℕ} (p : Partition n) (hk : p.parts.card = k) : Partition (n + k) :=
  Partition.ofSums (n + k) (p.parts.map (· + 1)) (by
    simp only [Multiset.sum_map_add, Multiset.map_id', Multiset.map_const', p.parts_sum, hk]
    simp [Multiset.sum_replicate])

/-- Helper to cast partition when sizes are equal. -/
def castPartition {n m : ℕ} (h : n = m) (p : Partition n) : Partition m where
  parts := p.parts
  parts_sum := by rw [← h]; exact p.parts_sum
  parts_pos := @p.parts_pos

/-- Extract the smaller part from a partition into 2 parts. -/
def smallerPartOf {n : ℕ} (p : Partition n) (_ : p.parts.card = 2) : ℕ :=
  p.parts.fold min n

/-- Construct a partition from a smaller part b. -/
def ofSmallerPart (n b : ℕ) (hb1 : 1 ≤ b) (hb2 : 2 * b ≤ n) : Partition n :=
  Partition.ofSums n {n - b, b} (by simp; omega)
/-! ### Generating functions -/


section GenFun

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]

end GenFun
/-! ### Odd parts and distinct parts

This section formalizes Euler's odd-distinct identity (Theorem \ref{thm.pars.odd-dist-equal}),
which states that the number of partitions of n into odd parts equals the number of
partitions of n into distinct parts.

#### Definition \ref{def.pars.odd-dist-parts}

* A **partition into odd parts** is a partition whose all parts are odd.
* A **partition into distinct parts** is a partition whose parts are all different.
* `p_odd(n)` = number of partitions of n into odd parts
* `p_dist(n)` = number of partitions of n into distinct parts

#### Theorem \ref{thm.pars.odd-dist-equal}: Euler's Odd-Distinct Identity

We have `p_odd(n) = p_dist(n)` for each n ∈ ℕ.

##### Generating Function Proof

The identity follows from the generating function identity:
```
∏_{i>0} (1-x^{2i-1})^{-1} = ∏_{k>0} (1+x^k)
```
The LHS generates partitions into odd parts (each odd k can appear any number of times).
The RHS generates partitions into distinct parts (each k appears 0 or 1 times).

##### Bijective Proof

**Map A: odd parts → distinct parts**
Given a partition λ into odd parts, repeatedly merge pairs of equal parts until no
equal parts remain. The result A(λ) is a partition into distinct parts.

Example: (5,5,3,1,1,1) → (10,3,2,1) by merging (5,5)→10 and (1,1)→2.

This is well-defined because merging equal odd parts produces even parts, and the
process terminates. The final partition has distinct parts because if k appears m times
in the original partition, then in A(λ), the parts 2^0·k, 2^1·k, 2^2·k, ... appear
according to the binary representation of m.

**Map B: distinct parts → odd parts**
Given a partition λ into distinct parts, repeatedly split even parts into halves until
only odd parts remain.

Example: (10,3,2,1) → (5,5,3,1,1,1) by splitting 10→(5,5) and 2→(1,1).

The maps A and B are mutually inverse, establishing the bijection.
-/


/-- A partition into odd parts is a partition whose all parts are odd.
    (Definition \ref{def.pars.odd-dist-parts} (a))

    For example, (7), (5,1,1), (3,3,1), (3,1,1,1,1), (1,1,1,1,1,1,1) are the
    partitions of 7 into odd parts. -/
def IsOddParts {n : ℕ} (p : Partition n) : Prop := ∀ i ∈ p.parts, Odd i

/-- A partition into distinct parts is a partition whose parts are all different.
    (Definition \ref{def.pars.odd-dist-parts} (b))

    For example, (7), (6,1), (5,2), (4,3), (4,2,1) are the partitions of 7 into
    distinct parts. Note that repeated parts are not allowed. -/
def IsDistinctParts {n : ℕ} (p : Partition n) : Prop := p.parts.Nodup

/-- The number of partitions of n into odd parts: `p_odd(n)`.
    (Definition \ref{def.pars.odd-dist-parts} (c))

    This counts the partitions of n where every part is an odd number.
    Uses Mathlib's `Nat.Partition.odds` which filters partitions by the
    predicate `¬Even` (equivalent to `Odd` for positive integers). -/
def oddPartsCount (n : ℕ) : ℕ := (odds n).card

/-- The number of partitions of n into distinct parts: `p_dist(n)`.
    (Definition \ref{def.pars.odd-dist-parts} (c))

    This counts the partitions of n where all parts are different (no repeats).
    Uses Mathlib's `Nat.Partition.distincts` which filters partitions by
    the `Nodup` predicate on the parts multiset. -/
def distinctPartsCount (n : ℕ) : ℕ := (distincts n).card

instance {n : ℕ} (p : Partition n) : Decidable (IsOddParts p) :=
  inferInstanceAs (Decidable (∀ i ∈ p.parts, Odd i))

instance {n : ℕ} (p : Partition n) : Decidable (IsDistinctParts p) :=
  inferInstanceAs (Decidable p.parts.Nodup)
/-! #### Examples from the textbook (following Definition \ref{def.pars.odd-dist-parts}) -/


/-- Example: `p_odd(7) = 5`. The partitions of 7 into odd parts are:
    (7), (5,1,1), (3,3,1), (3,1,1,1,1), (1,1,1,1,1,1,1). -/
example : oddPartsCount 7 = 5 := by native_decide

/-- Example: `p_dist(7) = 5`. The partitions of 7 into distinct parts are:
    (7), (6,1), (5,2), (4,3), (4,2,1). -/
example : distinctPartsCount 7 = 5 := by native_decide

/-- Example: `p_odd(0) = 1`. The only partition of 0 into odd parts is the empty partition. -/
example : oddPartsCount 0 = 1 := by native_decide

/-- Example: `p_dist(0) = 1`. The only partition of 0 into distinct parts is the empty partition. -/
example : distinctPartsCount 0 = 1 := by native_decide

/-- Example: `p_odd(3) = 2`. The partitions of 3 into odd parts are (3) and (1,1,1). -/
example : oddPartsCount 3 = 2 := by native_decide

/-- Example: `p_dist(3) = 2`. The partitions of 3 into distinct parts are (3) and (2,1). -/
example : distinctPartsCount 3 = 2 := by native_decide
/-! #### API for IsOddParts and IsDistinctParts -/
/-! ### Conjugation / Transposition of partitions -/


/-- The transpose (conjugate) of a partition.
    For a partition λ = (λ₁, λ₂, ..., λₖ), the transpose λᵗ is defined by:
    - The Young diagram of λᵗ is the transpose of the Young diagram of λ
    - Equivalently: (λᵗ)ᵢ = #{j : λⱼ ≥ i}

    The transpose satisfies:
    - |λᵗ| = |λ| (same size)
    - (λᵗ)ᵗ = λ (involution)
    - length(λᵗ) = largest part of λ
    - largest part of λᵗ = length(λ) -/
noncomputable def transpose {n : ℕ} (p : Partition n) : Partition n := by
  -- The transpose has parts: for each i from 1 to (largest part of p),
  -- the i-th part of the transpose is the number of parts of p that are ≥ i
  let largest := p.parts.fold max 0
  let newParts : Multiset ℕ := (Finset.range largest).val.map
    (fun i => (p.parts.filter (· > i)).card)
  refine ⟨newParts.filter (· > 0), ?_, ?_⟩
  · intro i hi
    simp only [Multiset.mem_filter] at hi
    exact hi.2
  · -- Prove sum equals n using double counting
    show (newParts.filter (· > 0)).sum = n
    have h1 : newParts.sum = n := by
      show ((Finset.range largest).val.map (fun i => (p.parts.filter (· > i)).card)).sum = n
      have heq : ((Finset.range largest).val.map (fun i => (p.parts.filter (· > i)).card)).sum =
                 (Finset.range largest).sum (fun i => (p.parts.filter (· > i)).card) := rfl
      rw [heq]
      have hp' : ∀ i ∈ p.parts, 0 < i := fun i hi => p.parts_pos hi
      have := sum_filter_card_eq_sum p.parts hp'
      rw [p.parts_sum] at this
      exact this
    rw [sum_filter_positive newParts]
    exact h1

section GenFun2

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]

end GenFun2
/-! ### Counting partitions by parts and largest part -/


/-- The count of partitions with exactly k parts and largest part ℓ, for a specific size n. -/
def partsAndLargestCount (k ℓ n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Partition n)).filter
    (fun p => p.numParts = k ∧ p.largestPart = ℓ)).card

/-- The total count of partitions with exactly k parts and largest part ℓ (summed over all sizes).
    The size ranges from k (minimum, when all parts are 1 except the largest) to k*ℓ (maximum,
    when all parts equal ℓ). -/
def partsAndLargestCountTotal (k ℓ : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc k (k * ℓ), partsAndLargestCount k ℓ n
/-! #### Helper lemmas for the bijection

The following lemmas provide infrastructure for the bijection proof in `partsAndLargestCountTotal_eq`.
They establish key properties of the forward map (Sym → Partition):
- `symToPartsMultiset`: constructs partition parts from a Sym
- `symToPartsMultiset_pos`: all parts are positive
- `symToPartsMultiset_card`: cardinality is k
- `symToPartsMultiset_fold_max`: largest part is ℓ
- `symToPartsMultiset_erase`: erasing ℓ recovers the Sym elements
- `symToPartsMultiset_sum_range`: sum lies in the valid range [k, k*ℓ]

The backward map (Partition → Sym) uses `Multiset.pmap` to map each part x in
`p.parts.erase ℓ` to `⟨x - 1, ...⟩ : Fin ℓ`, which is valid since all such parts
are in {1, ..., ℓ}.

The `Equiv` construction is completed in `partsAndLargestCountTotal_eq` using
`Equiv.ofBijective` with `toSigma_injective` and `toSigma_surj`. -/

variable {n : ℕ} in
/-- The multiset ℓ ::ₘ (s.val.map (fun x => x.val + 1)) for a Sym (Fin ℓ) n. -/
def symToPartsMultiset (ℓ : ℕ) (s : Sym (Fin ℓ) n) : Multiset ℕ :=
  ℓ ::ₘ (s.val.map (fun x => x.val + 1))

variable {n : ℕ} in

variable {n : ℕ} in

variable {n : ℕ} in

variable {n : ℕ} in
/-! #### Examples verifying the formula

The following examples verify the formula C(k+ℓ-2, k-1) against computed values:
- k=1, ℓ=1: C(0,0) = 1. Partition: (1).
- k=1, ℓ=5: C(4,0) = 1. Partition: (5).
- k=2, ℓ=1: C(1,1) = 1. Partition: (1,1).
- k=2, ℓ=2: C(2,1) = 2. Partitions: (2,1), (2,2).
- k=2, ℓ=3: C(3,1) = 3. Partitions: (3,1), (3,2), (3,3).
- k=3, ℓ=2: C(3,2) = 3. Partitions: (2,1,1), (2,2,1), (2,2,2).
-/


example : partsAndLargestCountTotal 1 1 = (1 + 1 - 2).choose (1 - 1) := by native_decide
example : partsAndLargestCountTotal 1 5 = (1 + 5 - 2).choose (1 - 1) := by native_decide
example : partsAndLargestCountTotal 2 1 = (2 + 1 - 2).choose (2 - 1) := by native_decide
example : partsAndLargestCountTotal 2 2 = (2 + 2 - 2).choose (2 - 1) := by native_decide
example : partsAndLargestCountTotal 2 3 = (2 + 3 - 2).choose (2 - 1) := by native_decide
example : partsAndLargestCountTotal 3 2 = (3 + 2 - 2).choose (3 - 1) := by native_decide
example : partsAndLargestCountTotal 3 3 = (3 + 3 - 2).choose (3 - 1) := by native_decide
example : partsAndLargestCountTotal 4 3 = (4 + 3 - 2).choose (4 - 1) := by native_decide
/-! ### Partition numbers and divisor sums -/


open ArithmeticFunction in
/-- The sum of divisors function σ(n) = ∑_{d|n} d.
    This is `ArithmeticFunction.sigma 1` in Mathlib. -/
abbrev divisorSum (n : ℕ) : ℕ := sigma 1 n

section DivisorSumRecurrence
/-!
## Proof of Theorem σ₁ (thm.pars.sigma1)

We prove the recurrence `n · p(n) = ∑_{k=1}^n σ(k) · p(n-k)` using generating functions.

### Proof outline (from the TeX source)

Define the generating functions:
- `P := ∑_{n≥0} p(n) x^n` (the partition generating function)
- `S := ∑_{k≥1} σ(k) x^k` (the divisor sum generating function)

The key identity is `X · P' = S · P`, which we prove using logarithmic derivatives.

Since `P = ∏_{k≥1} 1/(1-x^k)`, taking the logarithmic derivative gives:
```
  P'/P = ∑_{k≥1} loder(1/(1-x^k))
       = ∑_{k≥1} kx^{k-1}/(1-x^k)
       = ∑_{n≥1} σ(n) x^{n-1}
```

Multiplying by `xP` gives `xP' = SP`.

Comparing coefficients of `x^n` on both sides:
- LHS: coefficient of `x^n` in `xP'` is `n · p(n)`
- RHS: coefficient of `x^n` in `SP` is `∑_{k=1}^n σ(k) · p(n-k)`

This proves the theorem.
-/


/-- The partition generating function P = ∑_{n≥0} p(n) x^n, specialized to ℤ coefficients. -/
noncomputable def P : ℤ⟦X⟧ := genFun (fun _ _ => 1)

/-- The divisor sum generating function S = ∑_{k≥1} σ(k) x^k. -/
noncomputable def S : ℤ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else divisorSum n

end DivisorSumRecurrence

/-- Helper: sum of multiset minus another multiset. -/
theorem multiset_sum_sub_le {s t : Multiset ℕ} (h : t ≤ s) :
    (s - t).sum = s.sum - t.sum := by
  have hadd : s = (s - t) + t := (Multiset.sub_add_cancel h).symm
  calc (s - t).sum = (s - t).sum + t.sum - t.sum := by omega
    _ = ((s - t) + t).sum - t.sum := by rw [Multiset.sum_add]
    _ = s.sum - t.sum := by rw [← hadd]

/-- Helper: replicate is ≤ multiset if count is sufficient. -/
theorem replicate_le_of_count_ge {s : Multiset ℕ} {a : ℕ} {j : ℕ}
    (h : j ≤ s.count a) : Multiset.replicate j a ≤ s := by
  rw [Multiset.le_iff_count]
  intro b
  rw [Multiset.count_replicate]
  split_ifs with hba
  · subst hba; exact h
  · exact Nat.zero_le _
/-! #### Helper lemmas for partitionCount_divisorSum_restricted

These lemmas establish the key pieces needed for the double-counting proof:
1. **Bijection lemma**: Removing j copies of d from a partition gives a partition of n - d*j
2. **Count sum identity**: ∑_p count(d, p) = ∑_{j≥1} |{p : count(d,p) ≥ j}|
3. **Sum swap lemma**: Swap the order of summation over partitions and parts
4. **Divisor sum reindexing**: Transform ∑_k ∑_{d | k+1} to ∑_d ∑_{j : d*j ≤ n}
-/


/-- Remove j copies of element d from a partition, getting a partition of n - d*j.
    This is the forward direction of the bijection. -/
def removePartCopies {n : ℕ} (p : Partition n) (d j : ℕ) (_hd : d > 0) (hj : j ≤ p.parts.count d) :
    Partition (n - d * j) := by
  let newParts := p.parts - Multiset.replicate j d
  have hle : Multiset.replicate j d ≤ p.parts := replicate_le_of_count_ge hj
  have hsum : newParts.sum = n - d * j := by
    rw [multiset_sum_sub_le hle, p.parts_sum, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hpos : ∀ {x}, x ∈ newParts → 0 < x := by
    intro x hx
    have hx_in_orig : x ∈ p.parts := Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    exact p.parts_pos hx_in_orig
  exact ⟨newParts, hpos, hsum⟩

/-- Add j copies of element d to a partition, getting a partition of m + d*j.
    This is the backward direction of the bijection. -/
def addPartCopies {m : ℕ} (q : Partition m) (d j : ℕ) (hd : d > 0) :
    Partition (m + d * j) := by
  let newParts := q.parts + Multiset.replicate j d
  have hsum : newParts.sum = m + d * j := by
    simp only [newParts, Multiset.sum_add, q.parts_sum, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hpos : ∀ {x}, x ∈ newParts → 0 < x := by
    intro x hx
    simp only [newParts, Multiset.mem_add] at hx
    rcases hx with hx_q | hx_rep
    · exact q.parts_pos hx_q
    · simp only [Multiset.mem_replicate] at hx_rep
      rcases hx_rep with ⟨_, rfl⟩
      exact hd
  exact ⟨newParts, hpos, hsum⟩

end Nat.Partition
