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
import Def.Combinatorics.Enumerative.QBinomialFormulas.Part5
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

section Limits

open scoped PowerSeries.WithPiTopology

/-- The bijection between partitions with all parts ≤ k and partitions with at most k parts.

    This is a well-known combinatorial fact: the two sets are in bijection via
    Young diagram conjugation (transpose).

    For a partition p with parts [p₁, p₂, ..., pₘ] (sorted decreasing):
    - The conjugate partition has its i-th part equal to #{j : pⱼ ≥ i}
    - This is an involution that swaps "max part" with "number of parts"

    Key properties:
    - If all parts of p are ≤ k, then the conjugate has at most k parts
    - If p has at most k parts, then the conjugate has all parts ≤ k

    The proof uses YoungDiagram.transpose from Mathlib, which provides the conjugation
    operation on Young diagrams. -/
-- Helper: Young diagram card equals sum of row lengths
theorem youngDiagram_card_eq_rowLens_sum (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  simp only [YoungDiagram.card, YoungDiagram.rowLens]
  have hsum : (List.map μ.rowLen (List.range (μ.colLen 0))).sum =
              ∑ i ∈ range (μ.colLen 0), μ.rowLen i := by
    induction μ.colLen 0 with
    | zero => simp
    | succ m ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
                 List.sum_singleton, sum_range_succ]
      rw [ih]
  rw [hsum]
  conv_rhs => arg 2; ext i; rw [YoungDiagram.rowLen_eq_card]
  have hcells : μ.cells = (range (μ.colLen 0)).biUnion (fun i => μ.row i) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_biUnion, mem_range, YoungDiagram.mem_cells, YoungDiagram.mem_row_iff]
    constructor
    · intro hcell
      have hi : i < μ.colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen]
        exact μ.up_left_mem (le_refl i) (Nat.zero_le j) hcell
      exact ⟨i, hi, hcell, rfl⟩
    · intro ⟨i', hi', hcell, heq⟩
      exact heq ▸ hcell
  rw [hcells, Finset.card_biUnion]
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_iff_ne]
  intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
  simp only [YoungDiagram.mem_row_iff] at ha hc
  cases heq
  exact hij (ha.2.symm.trans hc.2)

-- Helper: ofRowLens card equals list sum
theorem ofRowLens_card_eq_sum (w : List ℕ) (hw : w.SortedGE) (hpos : ∀ x ∈ w, 0 < x) :
    (YoungDiagram.ofRowLens w hw).card = w.sum := by
  rw [youngDiagram_card_eq_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self hpos]

-- Helper: positivity of sorted parts
theorem parts_sort_pos' (m : ℕ) (p : Nat.Partition m) :
    ∀ x ∈ p.parts.sort (· ≥ ·), 0 < x := by
  intro x hx
  have : x ∈ p.parts := by simp only [Multiset.mem_sort] at hx; exact hx
  exact p.parts_pos this

-- Helper: sortedness of sorted parts
theorem parts_sort_sorted' (m : ℕ) (p : Nat.Partition m) :
    (p.parts.sort (· ≥ ·)).SortedGE :=
  (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE

-- Helper: transpose preserves card
theorem transpose_card' (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp only [YoungDiagram.card]
  have h : μ.transpose.cells = (Equiv.prodComm ℕ ℕ).finsetCongr μ.cells := rfl
  rw [h, Equiv.finsetCongr_apply, Finset.card_map]

end Limits
end QBinomialRec
end AlgebraicCombinatorics
