import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPieceMul
open IsDiscreteValuationRing


/--
[residueFieldMulMaximalIdealGradedPiece_residue_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean)
-/
@[path]
private lemma residueFieldMulMaximalIdealGradedPiece_residue_mk_eq
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {x : R}
  {i : ℕ}
  {y : ((IsLocalRing.maximalIdeal R) ^ i : Ideal R)} :
-- imply
  residueFieldMulMaximalIdealGradedPiece R (IsLocalRing.residue R x) i
    (Submodule.Quotient.mk y) =
    Submodule.Quotient.mk (x • y) := by
-- proof
  apply IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece_residue_mk R x i y

/--
[residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean)
-/
@[path]
private lemma residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul_eq
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra K (IsLocalRing.ResidueField R)]
  {i : ℕ} [Module K (MaximalIdealGradedPiece R i)] [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
  {a : IsLocalRing.ResidueField R} :
-- imply
  ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K).conj
    (Algebra.lmul K (IsLocalRing.ResidueField R) a) =
    (residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K := by
-- proof
  apply IsDiscreteValuationRing.residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul R i a

/--
[trace_residueFieldMulMaximalIdealGradedPiece](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean)
-/
@[path]
private lemma trace_residueFieldMulMaximalIdealGradedPiece_eq
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra K (IsLocalRing.ResidueField R)]
  {i : ℕ} [Module K (MaximalIdealGradedPiece R i)] [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
  {a : IsLocalRing.ResidueField R} :
-- imply
  LinearMap.trace K (MaximalIdealGradedPiece R i)
    ((residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K) =
    Algebra.trace K (IsLocalRing.ResidueField R) a := by
-- proof
  apply IsDiscreteValuationRing.trace_residueFieldMulMaximalIdealGradedPiece R i a


-- created on 2026-10-20
