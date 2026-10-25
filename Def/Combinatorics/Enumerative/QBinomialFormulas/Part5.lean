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
import Theorem.Combinatorics.Enumerative.QBinomialFormulas.Part3
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

section CountingSubspaces

variable {F : Type*} [Field F] [Fintype F]

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

-- Bijection between {v : Fin k → W // LinearIndependent F (Subtype.val ∘ v)} and
-- {v : Fin k → W // LinearIndependent F v}
noncomputable def linIndepEquiv (k : ℕ) (W : Submodule F V) :
    {v : Fin k → W // LinearIndependent F (Subtype.val ∘ v)} ≃
    {v : Fin k → W // LinearIndependent F v} := by
  refine Equiv.subtypeEquiv (Equiv.refl _) ?_
  intro v
  constructor
  · intro h
    exact LinearIndependent.of_comp W.subtype h
  · intro h
    exact h.map' W.subtype (Submodule.ker_subtype W)

-- Bijection between fiber and lin indep k-tuples in W
noncomputable def fiberEquiv (k : ℕ) (W : {W : Submodule F V // Module.finrank F W = k}) :
    {v : {v : Fin k → V // LinearIndependent F v} // spanMap k v = W} ≃
    {v : Fin k → W.val // LinearIndependent F v} := by
  refine (Equiv.ofBijective ?_ ⟨?_, ?_⟩).trans (linIndepEquiv k W.val)
  -- Forward map: given v with span(v) = W, restrict to W
  · intro ⟨⟨v, hv⟩, hvW⟩
    have heq : Submodule.span F (Set.range v) = W.val := by
      simp only [spanMap, Subtype.ext_iff] at hvW
      exact hvW
    refine ⟨fun i => ⟨v i, mem_of_spanMap_eq heq i⟩, ?_⟩
    simp only [Function.comp_def]
    exact hv
  -- Injective
  · intro ⟨⟨v1, hv1⟩, hvW1⟩ ⟨⟨v2, hv2⟩, hvW2⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    funext i
    have := congrFun heq i
    simp only [Subtype.mk.injEq] at this
    exact this
  -- Surjective
  · intro ⟨w, hw⟩
    let v : Fin k → V := Subtype.val ∘ w
    have hv : LinearIndependent F v := hw
    have hspan : Submodule.span F (Set.range v) = W.val := by
      have hle : Submodule.span F (Set.range v) ≤ W.val := by
        apply Submodule.span_le.mpr
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact (w i).prop
      have hfinrank : Module.finrank F (Submodule.span F (Set.range v)) = k := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_eq hle (hfinrank.trans W.prop.symm)
    refine ⟨⟨⟨v, hv⟩, ?_⟩, ?_⟩
    · simp only [spanMap, Subtype.ext_iff]
      exact hspan
    · simp only [Subtype.mk.injEq]
      ext i
      simp [v]

end CountingSubspaces

section Limits

/-- The number of partitions of n with at most k parts. -/
noncomputable def partitionCountAtMostKParts (n k : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // p.parts.card ≤ k}

end Limits
end QBinomialRec
end AlgebraicCombinatorics
