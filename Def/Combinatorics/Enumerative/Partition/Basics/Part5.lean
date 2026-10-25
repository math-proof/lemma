/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.Partition.Basics.Part4
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

end Nat.Partition
