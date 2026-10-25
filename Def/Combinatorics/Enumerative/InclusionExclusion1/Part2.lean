/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.Combinatorics.Enumerative.InclusionExclusion1.Part2
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

/-! ### Example 2: Derangements (Definition `def.pie.dera` and Theorem `thm.pie.count-der`)

A derangement is a permutation with no fixed points.

**Relationship to Mathlib:**
- Mathlib defines `derangements α : Set (Perm α)` in `Mathlib.Combinatorics.Derangements.Basic`
- Mathlib defines `numDerangements : ℕ → ℕ` in `Mathlib.Combinatorics.Derangements.Finite`
- Our `Derangement α` is definitionally equal to `↥(derangements α)` (the subtype)
- `Fintype.card (Derangement (Fin n))` equals `numDerangements n` (see `card_Derangement_eq`)

We provide the explicit `Derangement` type to make the connection to the textbook explicit.
The main theorems use Mathlib's `numDerangements` directly.
-/


/-- **Definition `def.pie.dera`**: A derangement of a type `α` is a permutation with no fixed points.

This is definitionally equal to `↥(derangements α)` from `Mathlib.Combinatorics.Derangements.Basic`.

**Textbook definition:** "A derangement of a set X means a permutation of X that has no fixed points."

**Examples from the textbook:**
- D₀ = 1: The identity on ∅ is a derangement (vacuously no fixed points)
- D₁ = 0: The identity on {0} fixes 0, so it's not a derangement
- D₂ = 1: Only the swap (0 1) is a derangement
- D₃ = 2: The two 3-cycles (0 1 2) and (0 2 1) are derangements -/
def Derangement (α : Type*) := {σ : Equiv.Perm α // ∀ x, σ x ≠ x}

end AlgebraicCombinatorics.InclusionExclusion
