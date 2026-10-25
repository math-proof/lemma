/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.QBinomialBasic.Part4
import Theorem.Combinatorics.Enumerative.QBinomialFormulas
open Polynomial Finset BigOperators

/-!
# q-Binomial Formulas

This file formalizes the q-binomial formulas from the Algebraic Combinatorics text,
including:
- The first q-binomial theorem
- The second q-binomial theorem (Potter's binomial theorem)
- Counting subspaces of finite-dimensional vector spaces over finite fields
- Limits of q-binomial coefficients

## Main Definitions (in namespace `AlgebraicCombinatorics.QBinomialRec`)

* `qBinomial`: The q-binomial coefficient `[n choose k]_q`, defined via q-Pascal recurrence
* `qFactorial`: The q-factorial `[n]_q!`
* `qNat`: The q-analog of natural number `[n]_q`

**Namespace structure:** All definitions in this file are in the sub-namespace
`AlgebraicCombinatorics.QBinomialRec` to avoid conflicts with the canonical definitions
in `QBinomialBasic.lean`. The canonical definitions use the monotone function sum formula,
while this file uses the q-Pascal recurrence. Both are equivalent (see `qBinomial_eq_sum_monotone`).

To use definitions from this file:
- Use full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
- Or open the namespace: `open AlgebraicCombinatorics.QBinomialRec`

## Main Results

* `qBinomial_eq_sum_monotone`: Equivalence to the monotone function sum definition
* `qBinomial_eq_sum_subsets`: Equivalence to the subset sum formula
* `qBinomial_first_theorem`: The first q-binomial theorem
* `qBinomial_second_theorem`: The second q-binomial theorem (Potter's binomial theorem)
* `qBinomial_subspace_count`: The q-binomial coefficient counts k-dimensional subspaces
* `qBinomial_limit`: The limit of q-binomial coefficients as n → ∞

## References

* Section on q-binomial formulas from Algebraic Combinatorics lecture notes
* See also `QBinomialBasic.lean` for the canonical definition and basic properties
-/


/-!
## Sub-namespace for Recursive q-Binomial Definitions

The definitions `qNat`, `qFactorial`, `qBinomial`, and related theorems in this file
use the q-Pascal recurrence, which is different from the monotone function sum
definition in `QBinomialBasic.lean`. To avoid namespace conflicts when both files
are imported together, these definitions are placed in the `QBinomialRec` sub-namespace.

The equivalence between the two definitions is proven in `qBinomial_eq_sum_monotone`.

To use these definitions, either:
1. Open the namespace: `open AlgebraicCombinatorics.QBinomialRec`
2. Use the full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
-/

/-!
### Definition def.pars.qbinom.qint: q-integers and q-factorials

This section formalizes the q-analogs of integers and factorials from Definition 2.3.2.

**Part (a)**: The q-integer `[n]_q = q^0 + q^1 + ... + q^{n-1} ∈ ℤ[q]`

**Part (b)**: The q-factorial `[n]_q! = [1]_q · [2]_q · ... · [n]_q ∈ ℤ[q]`

**Part (c)**: For any element `a` of a ring `A`, `[n]_a` and `[n]_a!` denote the results
of substituting `a` for `q` in `[n]_q` and `[n]_q!`, respectively.

### Remark rmk.pars.qbinom.qint.frac

For any `n ∈ ℕ`:
- `[n]_q = (1 - q^n)/(1 - q)` (in ℤ⟦q⟧ or in the field of rational functions)
- `[n]_1 = n`
- `[n]_1! = n!`
-/


namespace AlgebraicCombinatorics

namespace QBinomialRec

section CombinatoricDefinition

/-- Forward bijection for q-Pascal: subtract 1 from each part of a partition with exactly k+1 parts.
    Uses `Nat.Partition.ofSums` to filter out zeros. -/
noncomputable def subtractOnePartition (s k m : ℕ) (p : Nat.Partition s)
    (hp : p ∈ partitionsInBoxExact s (k + 1) m) : Nat.Partition (s - (k + 1)) := by
  have hparts : p.parts.card = k + 1 := by
    simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp
    exact hp.1
  have hpos : ∀ x ∈ p.parts, x ≥ 1 := fun x hx => p.parts_pos hx
  let newParts := p.parts.map (· - 1)
  have hsum : newParts.sum = s - (k + 1) := by
    simp only [newParts]
    rw [multiset_sum_sub_one p.parts hpos, p.parts_sum, hparts]
  exact Nat.Partition.ofSums (s - (k + 1)) newParts hsum

/-- Inverse bijection for q-Pascal: add 1 to each part and pad with 1s to get exactly k+1 parts. -/
noncomputable def addOnePartition (t k m : ℕ) (q : Nat.Partition t)
    (hq : q ∈ partitionsInBox t (k + 1) (m - 1)) : Nat.Partition (t + (k + 1)) := by
  have hlen : q.parts.card ≤ k + 1 := by
    simp only [partitionsInBox, mem_filter, mem_univ, true_and] at hq
    simp only [partitionLengthLeq] at hq
    exact hq.1
  let addedParts := q.parts.map (· + 1)
  let extraOnes := Multiset.replicate (k + 1 - q.parts.card) 1
  let newParts := addedParts + extraOnes
  have hsum : newParts.sum = t + (k + 1) := by
    simp only [newParts, addedParts, extraOnes]
    simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
    have h1 : (q.parts.map (· + 1)).sum = q.parts.sum + q.parts.card := by
      induction q.parts using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        omega
    rw [h1, q.parts_sum]
    omega
  have hpos : ∀ i ∈ newParts, 0 < i := by
    intro i hi
    simp only [newParts, addedParts, extraOnes, Multiset.mem_add] at hi
    rcases hi with hi_add | hi_extra
    · simp only [Multiset.mem_map] at hi_add
      obtain ⟨j, _, hj_eq⟩ := hi_add
      omega
    · simp only [Multiset.mem_replicate] at hi_extra
      omega
  exact ⟨newParts, @hpos, hsum⟩

/-- The q-binomial coefficient as a polynomial in ℤ[q].
    (Definition def.pars.qbinom.qbinom (a))

    `[n choose k]_q = ∑_{λ} q^|λ|`

    where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

    This is a polynomial (not just a formal power series) because there are
    finitely many such partitions - they all fit in a k × (n-k) box, so their
    size is at most k · (n-k).

    When k > n, this is 0 (the empty sum, since n - k < 0 means no partitions qualify). -/
noncomputable def qBinomialPolyDef (n k : ℕ) : Polynomial ℤ :=
  if k ≤ n then
    ∑ size ∈ range (k * (n - k) + 1),
      (countPartitionsInBox size k (n - k)) • (Polynomial.X : Polynomial ℤ) ^ size
  else 0

variable {R : Type*} [CommRing R]

/-- The q-binomial coefficient evaluated at a ring element.
    (Definition def.pars.qbinom.qbinom (b))

    `[n choose k]_a = ∑_{λ} a^|λ|`

    where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

    This is the result of substituting `a` for `q` in the polynomial `[n choose k]_q`. -/
noncomputable def qBinomialEval (n k : ℕ) (a : R) : R :=
  (qBinomialPolyDef n k).eval₂ (Int.castRingHom R) a

/-- Alternative definition: directly sum over partitions. -/
def qBinomialEvalDirect (n k : ℕ) (a : R) : R :=
  if k ≤ n then
    ∑ size ∈ range (k * (n - k) + 1),
      (countPartitionsInBox size k (n - k)) • a ^ size
  else 0

end CombinatoricDefinition
end QBinomialRec
end AlgebraicCombinatorics
