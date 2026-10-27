import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.DiscreteValuationRing.MaximalIdealGradedPieceMul
open IsDiscreteValuationRing


namespace IsDiscreteValuationRing

/--
[residueFieldMulMaximalIdealGradedPiece_residue_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean)
-/
@[path]
lemma residueFieldMulMaximalIdealGradedPiece_residue_mk
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {x : R}
  {i : ℕ}
  {y : ((IsLocalRing.maximalIdeal R) ^ i : Ideal R)} :
-- imply
  residueFieldMulMaximalIdealGradedPiece R (IsLocalRing.residue R x) i
    (Submodule.Quotient.mk y) =
    Submodule.Quotient.mk (x • y) := by
-- proof
  simp only [residueFieldMulMaximalIdealGradedPiece, LinearMap.lsmul_apply]
  exact Module.Quotient.mk_smul_mk _ _ x y

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/--
[residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean)
-/
@[path]
lemma residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra K (IsLocalRing.ResidueField R)]
  {i : ℕ} [Module K (MaximalIdealGradedPiece R i)] [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
  {a : IsLocalRing.ResidueField R} :
-- imply
  ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K).conj
    (Algebra.lmul K (IsLocalRing.ResidueField R) a) =
    (residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K := by
-- proof
  refine LinearMap.ext fun y => ?_
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.restrictScalars_symm_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply', LinearMap.restrictScalars_apply,
    residueFieldMulMaximalIdealGradedPiece, LinearMap.lsmul_apply]
  rw [← smul_eq_mul, map_smul, LinearEquiv.apply_symm_apply]

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/--
[trace_residueFieldMulMaximalIdealGradedPiece](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealGradedPieceMul.lean)
-/
@[path]
lemma trace_residueFieldMulMaximalIdealGradedPiece
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra K (IsLocalRing.ResidueField R)]
  {i : ℕ} [Module K (MaximalIdealGradedPiece R i)] [IsScalarTower K (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i)]
  {a : IsLocalRing.ResidueField R} :
-- imply
  LinearMap.trace K (MaximalIdealGradedPiece R i)
    ((residueFieldMulMaximalIdealGradedPiece R a i).restrictScalars K) =
    Algebra.trace K (IsLocalRing.ResidueField R) a := by
-- proof
  rw [Algebra.trace_apply, ← LinearMap.trace_conj'
    (Algebra.lmul K (IsLocalRing.ResidueField R) a)
    ((residueFieldLinearEquivMaximalIdealGradedPiece R i).restrictScalars K),
    residueFieldLinearEquivMaximalIdealGradedPiece_conj_lmul]

end IsDiscreteValuationRing


-- created on 2026-10-20
-- updated on 2026-10-26
