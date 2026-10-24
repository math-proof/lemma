/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
/-!
# Boolean Möbius Inversion

This file formalizes the Boolean Möbius inversion formula, also known as the
Möbius inversion formula for the Boolean lattice.

## Main Results

* `booleanMobiusInversion`: Given functions `a` and `b` on subsets of a finite set `S`
  where `b I = ∑ J ⊆ I, a J` for all `I ⊆ S`, we have `a I = ∑ J ⊆ I, (-1)^|I \ J| * b J`

* `alternatingSum_superset_eq_iverson_a`: For `P ⊆ Q`, we have
  `∑_{I : P ⊆ I ⊆ Q} (-1)^|I| = (-1)^|P| * [P = Q]`

* `alternatingSum_superset_eq_iverson_b`: For `P ⊆ Q`, we have
  `∑_{I : P ⊆ I ⊆ Q} (-1)^|Q \ I| = [P = Q]`

## References

* Source: `AlgebraicCombinatorics/tex/SignedCounting/InclusionExclusion2.tex`
  - Section: `subsec.sign.pie.moeb-bool`
  - Theorem `thm.pie.moeb`
  - Lemma `lem.pie.two-sets-altsum`

## Tags

inclusion-exclusion, Möbius inversion, Boolean lattice, alternating sum
-/


open Finset BigOperators

variable {α : Type*} [DecidableEq α]

namespace BooleanMobius
/-! ### Alternating Sums over Supersets

These lemmas establish the key combinatorial identities needed for the Boolean
Möbius inversion formula.

The key insight is that for P ⊆ Q, the sum `∑_{I : P ⊆ I ⊆ Q} (-1)^|I|` equals
`(-1)^|P|` when P = Q and 0 otherwise. The proof uses the bijection from
`(Q \ P).powerset` to `Icc P Q` (via `Icc_eq_image_powerset`) and then applies
Mathlib's `sum_powerset_neg_one_pow_card`.
-/
/-! ### Boolean Möbius Inversion

The main theorem states that if `b I = ∑_{J ⊆ I} a J` for all I ⊆ S, then
we can recover `a` from `b` via `a I = ∑_{J ⊆ I} (-1)^|I \ J| b J`.

This is a fundamental result in combinatorics, generalizing the inclusion-exclusion
principle.
-/

end BooleanMobius
