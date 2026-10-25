import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
open Set SimpleGraph StatMech StatMech.Onsager


/--
[ons_rectDualIntPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma ons_rectDualIntPoint_injective_eq
  {M N : Nat} :
-- imply
  Function.Injective (ons_rectDualIntPoint : ons_RectDualVertex M N -> Int × Int) := by
-- proof
  apply StatMech.Onsager.ons_rectDualIntPoint_injective

/--
[ons_rectDualComplexPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma ons_rectDualComplexPoint_injective_eq
  {M N : Nat} :
-- imply
  Function.Injective (ons_rectDualComplexPoint : ons_RectDualVertex M N -> Complex) := by
-- proof
  apply StatMech.Onsager.ons_rectDualComplexPoint_injective

/--
[ons_rectDualIntPoint_snd_eq_add_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma ons_rectDualIntPoint_snd_eq_add_step_eq
  {M N : Nat}
  {dart : (ons_rectDualGraph M N).Dart} :
-- imply
  ons_rectDualIntPoint dart.snd = ons_rectDualIntPoint dart.fst + triangularIntStep (ons_rectDualDartDirection dart) := by
-- proof
  apply StatMech.Onsager.ons_rectDualIntPoint_snd_eq_add_step dart

/--
[coe_ons_rectDual_X_sq_eq_canonicalKWDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma coe_ons_rectDual_X_sq_eq_canonicalKWDet_eq
  {M N : Nat}
  {x : Real} :
-- imply
  (ons_X (ons_rectDualGraph M N) x : Complex) ^ 2 = ons_rectDualCanonicalKWDet M N x := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDual_X_sq_eq_canonicalKWDet M N x

/--
[coe_ons_rectDualPath_sourceX_sq_eq_canonicalDefectKWDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma coe_ons_rectDualPath_sourceX_sq_eq_canonicalDefectKWDet_eq
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {x : Real}
-- given
  (hx : x ≠ 0) :
-- imply
  (ons_sourceX (ons_rectDualGraph M N) {path.source, path.target} x : Complex) ^ 2 = (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card) * ons_rectDualPathCanonicalDefectKWDet path x := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDualPath_sourceX_sq_eq_canonicalDefectKWDet path hx

/--
[ons_rectDualPath_canonicalDefectKWDet_eq_signedLoopObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma ons_rectDualPath_canonicalDefectKWDet_eq_signedLoopObservable_eq
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {x : Real}
-- given
  (hx : x ≠ 0) :
-- imply
  ons_rectDualPathCanonicalDefectKWDet path x = ons_rectDualPathSignedLoopObservable path x := by
-- proof
  apply StatMech.Onsager.ons_rectDualPath_canonicalDefectKWDet_eq_signedLoopObservable path hx

/--
[coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio_eq
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0 (fun spin => StatMech.Ising.spin spin path.source * StatMech.Ising.spin spin path.target) : Complex) ^ 2 = ((Real.tanh beta : Complex) ^ (2 * (ons_rectDualPathDefect path).card) * ons_rectDualPathCanonicalDefectKWDet path (Real.tanh beta)) / ons_rectDualCanonicalKWDet M N (Real.tanh beta) := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio path hbeta

/--
[coe_ons_rectDualPath_criticalTwoPoint_sq_eq_canonicalKWDet_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean)
-/
@[path]
private lemma coe_ons_rectDualPath_criticalTwoPoint_sq_eq_canonicalKWDet_ratio_eq
  {M N : Nat}
  {path : ons_RectDualPath M N} :
-- imply
  (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0 (fun spin => StatMech.Ising.spin spin path.source * StatMech.Ising.spin spin path.target) : Complex) ^ 2 = ((ons_signedLoopCriticalWeight : Complex) ^ (2 * (ons_rectDualPathDefect path).card) * ons_rectDualPathCanonicalDefectKWDet path ons_signedLoopCriticalWeight) / ons_rectDualCanonicalKWDet M N ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDualPath_criticalTwoPoint_sq_eq_canonicalKWDet_ratio path


-- created on 2026-10-23
