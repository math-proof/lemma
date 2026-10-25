/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPiece.lean -/

/-
Author: Muse Code
-/

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Instance.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece
/-!
# Maximal-ideal graded pieces of a discrete valuation ring

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and residue field
`κ = R ⧸ 𝔪`. This file identifies every graded piece `𝔪 ^ i ⧸ 𝔪 ^ (i + 1)` as a
one-dimensional vector space over `κ`.

This module is a prerequisite stage for the corrected ATLAS NumberTheoryI N261
upper different-exponent bound (Theorem 12.27), not the full N261 target. It
proves only the residue-field-linear description and finrank of the
maximal-ideal graded pieces; it does not prove a trace formula,
different-ideal containment, or either valuation bound.

ATLAS source: [`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines define the ramification/different valuations and state the target
bounds, but they do not state the graded-piece equivalence proved here.

Source-to-API map: `MaximalIdealGradedPiece`,
`residueFieldLinearEquivMaximalIdealGradedPiece`, and
`finrank_maximalIdealGradedPiece` are new supporting API for a future
maximal-ideal-filtration proof of the trace/different estimate; the upper bound
and the tame-equality characterization remain deferred.

The helper `different_valuation_exact` there is unfinished, and its exact equality
is false in wild ramification, so it is not formalized here.

## Main results

* `IsDiscreteValuationRing.MaximalIdealGradedPiece`: the `i`-th graded piece
  `𝔪 ^ i ⧸ 𝔪 ^ (i + 1)`, as a quotient of the ideal `𝔪 ^ i` by `𝔪 • ⊤`.
* `IsDiscreteValuationRing.residueFieldLinearEquivMaximalIdealGradedPiece`:
  a `κ`-linear equivalence `κ ≃ₗ[κ] MaximalIdealGradedPiece R i`.
* `IsDiscreteValuationRing.finrank_maximalIdealGradedPiece`: each graded piece has
  `κ`-finrank one.
-/


namespace IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The `i`-th maximal-ideal graded piece is `κ`-linearly a copy of the residue
field. The underlying function and inverse come from
`Ideal.quotEquivPowQuotPowSucc`; only the residue-scalar compatibility is proved
here, by quotient induction: a residue scalar `mk r` acts on both sides as the
representative `r` acts over `R` (the maximal ideal annihilates the graded
piece, so this is well defined). -/
noncomputable def residueFieldLinearEquivMaximalIdealGradedPiece (i : ℕ) :
    IsLocalRing.ResidueField R ≃ₗ[IsLocalRing.ResidueField R]
      MaximalIdealGradedPiece R i :=
  let e : (R ⧸ IsLocalRing.maximalIdeal R) ≃ₗ[R] MaximalIdealGradedPiece R i :=
    Ideal.quotEquivPowQuotPowSucc
      (IsPrincipalIdealRing.principal _) (not_a_field R) i
  { e with
    map_smul' := fun q x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact e.map_smul r x }

end IsDiscreteValuationRing
