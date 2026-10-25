/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.Partition.Basics.Part5
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

end Nat.Partition
