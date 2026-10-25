/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.InclusionExclusion1.Part2
open Finset BigOperators Nat

/-!
# The Principles of Inclusion and Exclusion

This file formalizes the inclusion-exclusion principles and their applications from
Section `sec.sign.pie` of the Algebraic Combinatorics notes.

## Main results

### Size version (Theorem `thm.pie.1`)
The size version of PIE states that for a finite set `U` and subsets `A₁, ..., Aₙ`:
  |{u ∈ U : u ∉ Aᵢ for all i}| = ∑_{I ⊆ [n]} (-1)^|I| |{u ∈ U : u ∈ Aᵢ for all i ∈ I}|

This is already available in Mathlib as `Finset.inclusion_exclusion_card_inf_compl`.

### Applications

* `numSurj` - The number of surjective maps from `[m]` to `[n]` (Theorem `thm.pie.count-sur`)
* `numSurj_formula` - The formula: ∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)^m
* Corollaries about the surjection count (`cor.pie.count-sur.cors`)
* `Derangement` - Permutations with no fixed points (Definition `def.pie.dera`)
* `numDerangements_formula` - The derangement count formula (Theorem `thm.pie.count-der`)
* `totient_eq_prod_one_sub_inv` - Euler's totient formula (Theorem `thm.pie.euler-tot`)

### Weighted version (Theorem `thm.pie.2`)
The weighted version generalizes the size version by replacing cardinalities with weighted sums.
This is already available in Mathlib as `Finset.inclusion_exclusion_sum_inf_compl`.

## References

* Section `sec.sign.pie` of the Algebraic Combinatorics notes
* Mathlib's `Mathlib.Combinatorics.Enumerative.InclusionExclusion`
-/


namespace AlgebraicCombinatorics.InclusionExclusion

instance {α : Type*} [DecidableEq α] [Fintype α] : Fintype (Derangement α) :=
  Subtype.fintype _

end AlgebraicCombinatorics.InclusionExclusion
