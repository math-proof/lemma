/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean -/

/-
Author: Muse Code
-/

import Mathlib.RingTheory.Trace.Defs
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece
/-!
# Residue-field multiplication on maximal-ideal graded pieces

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and residue field
`κ = R ⧸ 𝔪`. This file equips every graded piece `𝔪 ^ i ⧸ 𝔪 ^ (i + 1)` with
multiplication by a residue-field scalar, as a `κ`-linear endomorphism, together
with the representative formula showing it acts as representative
multiplication on the quotient.

This module is a prerequisite stage for the corrected ATLAS NumberTheoryI N261
upper different-exponent bound (Theorem 12.27), not the full N261 target. It
proves the multiplication definition, the representative formula, the
base-change conjugacy statement, and the graded-piece trace statement; the
quotient filtered-trace theorem, the different-ideal containment, either
valuation bound, and the tame equality remain deferred.

ATLAS source: [`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines define the ramification/different valuations and state the target
bounds, but they do not state the graded-piece multiplication proved here.

Source-to-API map: `residueFieldMulMaximalIdealGradedPiece`,
`residueFieldMulMaximalIdealGradedPiece_residue_mk`,
`residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul`, and
`trace_residueFieldMulMaximalIdealGradedPiece` are new supporting API for a
future maximal-ideal-filtration proof of the trace/different estimate; the
quotient filtered-trace theorem, the different containment, the valuation
bounds, and the tame-equality characterization remain deferred.

## Main results

* `IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece`:
  multiplication by a residue-field scalar as a `κ`-linear endomorphism of the
  `i`-th graded piece.
* `IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece_residue_mk`:
  multiplication by `residue x` acts on a quotient representative as the
  representative `R`-scalar action `x • ·`.
* `IsDiscreteValuationRing.residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul`:
  after restricting scalars to a base field `K`, the graded-piece equivalence
  conjugates residue-field left multiplication to the graded-piece
  multiplication endomorphism.
* `IsDiscreteValuationRing.trace_residueFieldMulMaximalIdealGradedPiece`:
  after restricting scalars to a base field `K`, the linear trace of the
  graded-piece multiplication endomorphism equals the algebra trace of the
  residue scalar.
-/

namespace IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Multiplication by a residue-field scalar on the `i`-th maximal-ideal graded
piece, as a `κ`-linear endomorphism. This is new prerequisite support for the
corrected ATLAS N261 filtered-trace route (whose graded-piece trace statement
is proved below), not a source theorem. -/
noncomputable def residueFieldMulMaximalIdealGradedPiece
    (a : IsLocalRing.ResidueField R) (i : ℕ) :
    Module.End (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i) :=
  LinearMap.lsmul _ _ a

/-- Representative formula: multiplication by `residue x` acts on a quotient
representative as the representative `R`-scalar action `x • ·`. This is the
bridge from residue scalar multiplication to actual multiplication on the
quotient. -/
@[simp]
theorem residueFieldMulMaximalIdealGradedPiece_residue_mk
    (x : R) (i : ℕ) (y : ((IsLocalRing.maximalIdeal R) ^ i : Ideal R)) :
    residueFieldMulMaximalIdealGradedPiece R (IsLocalRing.residue R x) i
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x • y) := by
  simp only [residueFieldMulMaximalIdealGradedPiece, LinearMap.lsmul_apply]
  exact Module.Quotient.mk_smul_mk _ _ x y

/-- Base-change conjugacy: after restricting scalars to a base field `K`, the
graded-piece equivalence conjugates residue-field left multiplication to the
graded-piece multiplication endomorphism. New prerequisite support for the
corrected ATLAS N261 filtered-trace route, not a source theorem. -/
theorem residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul
    {K : Type*} [Field K] [Algebra K (IsLocalRing.ResidueField R)]
    (i : ℕ) [Module K (MaximalIdealGradedPiece R i)]
    [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
    (a : IsLocalRing.ResidueField R) :
    ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K).conj
        (Algebra.lmul K (IsLocalRing.ResidueField R) a) =
      (residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K := by
  refine LinearMap.ext fun y => ?_
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.restrictScalars_symm_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply', LinearMap.restrictScalars_apply,
    residueFieldMulMaximalIdealGradedPiece, LinearMap.lsmul_apply]
  rw [← smul_eq_mul, map_smul, LinearEquiv.apply_symm_apply]

/-- Graded-piece trace: after restricting scalars to a base field `K`, the
linear trace of the graded-piece multiplication endomorphism equals the
algebra trace of the residue scalar. New prerequisite support for the
corrected ATLAS N261 filtered-trace route, not a source theorem. -/
theorem trace_residueFieldMulMaximalIdealGradedPiece
    {K : Type*} [Field K] [Algebra K (IsLocalRing.ResidueField R)]
    (i : ℕ) [Module K (MaximalIdealGradedPiece R i)]
    [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
    (a : IsLocalRing.ResidueField R) :
    LinearMap.trace K (MaximalIdealGradedPiece R i)
        ((residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K) =
      Algebra.trace K (IsLocalRing.ResidueField R) a := by
  rw [Algebra.trace_apply, ← LinearMap.trace_conj'
    (Algebra.lmul K (IsLocalRing.ResidueField R) a)
    ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K),
    residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul]

end IsDiscreteValuationRing
