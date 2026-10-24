/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean -/

/-
Author: Muse Code
-/

import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPieceMul
import Lemma.Int.DiscreteValuationRing.MaximalIdealGradedPieceMul

/-!
# Tests for residue-field multiplication on maximal-ideal graded pieces

These examples exercise the four public API components of
`MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealGradedPieceMul`: the
residue-field multiplication endomorphism
`residueFieldMulMaximalIdealGradedPiece`, its representative formula
`residueFieldMulMaximalIdealGradedPiece_residue_mk`, the base-change
conjugacy theorem
`residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul`, and the
graded-piece trace theorem `trace_residueFieldMulMaximalIdealGradedPiece`.
-/


open IsLocalRing IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The residue-field multiplication endomorphism applies as stated. -/
noncomputable example (a : ResidueField R) (i : ℕ) :
    Module.End (ResidueField R) (MaximalIdealGradedPiece R i) :=
  residueFieldMulMaximalIdealGradedPiece R a i

/-- The representative formula applies as stated. -/
example (x : R) (i : ℕ) (y : ((maximalIdeal R) ^ i : Ideal R)) :
    residueFieldMulMaximalIdealGradedPiece R (IsLocalRing.residue R x) i
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x • y) :=
  residueFieldMulMaximalIdealGradedPiece_residue_mk R x i y

/-- The base-change conjugacy theorem applies as stated. -/
example {K : Type*} [Field K] [Algebra K (ResidueField R)] (i : ℕ)
    [Module K (MaximalIdealGradedPiece R i)]
    [IsScalarTower K (ResidueField R) (MaximalIdealGradedPiece R i)]
    (a : ResidueField R) :
    ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K).conj
        (Algebra.lmul K (ResidueField R) a) =
      (residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K :=
  residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul R i a

/-- The graded-piece trace theorem applies as stated. -/
example {K : Type*} [Field K] [Algebra K (ResidueField R)] (i : ℕ)
    [Module K (MaximalIdealGradedPiece R i)]
    [IsScalarTower K (ResidueField R) (MaximalIdealGradedPiece R i)]
    (a : ResidueField R) :
    LinearMap.trace K (MaximalIdealGradedPiece R i)
        ((residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K) =
      Algebra.trace K (ResidueField R) a :=
  trace_residueFieldMulMaximalIdealGradedPiece R i a
