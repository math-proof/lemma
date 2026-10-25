import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[ons_rectDualPathDefect_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma ons_rectDualPathDefect_subset_edgeFinset_eq
  {M N : Nat}
  {path : ons_RectDualPath M N} :
-- imply
  ons_rectDualPathDefect path ⊆ (ons_rectDualGraph M N).edgeFinset := by
-- proof
  apply StatMech.Onsager.ons_rectDualPathDefect_subset_edgeFinset path

/--
[ons_rectDualPathDefect_hasOddBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma ons_rectDualPathDefect_hasOddBoundary_eq
  {M N : Nat}
  {path : ons_RectDualPath M N} :
-- imply
  HasOddBoundary (ons_rectDualPathDefect path) {path.source, path.target} := by
-- proof
  apply StatMech.Onsager.ons_rectDualPathDefect_hasOddBoundary path

/--
[ons_rectDualPathDefectWeight_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma ons_rectDualPathDefectWeight_of_mem_eq
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {x : Real}
  {edge : Sym2 (ons_RectDualVertex M N)}
-- given
  (hedge : edge ∈ ons_rectDualPathDefect path) :
-- imply
  ons_rectDualPathDefectWeight path x edge = (x : Complex)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_rectDualPathDefectWeight_of_mem path x hedge

/--
[ons_rectDualPathDefectWeight_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma ons_rectDualPathDefectWeight_of_not_mem_eq
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {x : Real}
  {edge : Sym2 (ons_RectDualVertex M N)}
-- given
  (hedge : edge ∉ ons_rectDualPathDefect path) :
-- imply
  ons_rectDualPathDefectWeight path x edge = (x : Complex) := by
-- proof
  apply StatMech.Onsager.ons_rectDualPathDefectWeight_of_not_mem path x hedge

/--
[coe_ons_rectDual_X_sq_eq_kwDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma coe_ons_rectDual_X_sq_eq_kwDet_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {x : Real} :
-- imply
  (ons_X (ons_rectDualGraph M N) x : Complex) ^ 2 = ons_rectDualKWDet embedding x := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDual_X_sq_eq_kwDet embedding x

/--
[coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N}
  {x : Real}
-- given
  (hx : x ≠ 0) :
-- imply
  (ons_sourceX (ons_rectDualGraph M N) {path.source, path.target} x : Complex) ^ 2 = (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card) * ons_rectDualPathDefectKWDet embedding path x := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet embedding path hx

/--
[ons_rectDualPath_defectKWDet_eq_signedLoopObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma ons_rectDualPath_defectKWDet_eq_signedLoopObservable_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N}
  {x : Real}
-- given
  (hx : x ≠ 0) :
-- imply
  ons_rectDualPathDefectKWDet embedding path x = ons_rectDualPathSignedLoopObservable path x := by
-- proof
  apply StatMech.Onsager.ons_rectDualPath_defectKWDet_eq_signedLoopObservable embedding path hx

/--
[coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0 (fun spin => StatMech.Ising.spin spin path.source * StatMech.Ising.spin spin path.target) : Complex) ^ 2 = ((Real.tanh beta : Complex) ^ (2 * (ons_rectDualPathDefect path).card) * ons_rectDualPathDefectKWDet embedding path (Real.tanh beta)) / ons_rectDualKWDet embedding (Real.tanh beta) := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio embedding path hbeta

/--
[coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N} :
-- imply
  (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0 (fun spin => StatMech.Ising.spin spin path.source * StatMech.Ising.spin spin path.target) : Complex) ^ 2 = ((ons_signedLoopCriticalWeight : Complex) ^ (2 * (ons_rectDualPathDefect path).card) * ons_rectDualPathDefectKWDet embedding path ons_signedLoopCriticalWeight) / ons_rectDualKWDet embedding ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio embedding path

/--
[ons_rectDualPath_critical_defectKWDet_eq_signedLoopObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean)
-/
@[path]
private lemma ons_rectDualPath_critical_defectKWDet_eq_signedLoopObservable_eq
  {M N : Nat}
  {embedding : KWStraightLineEmbedding (ons_rectDualGraph M N)}
  {path : ons_RectDualPath M N} :
-- imply
  ons_rectDualPathDefectKWDet embedding path ons_signedLoopCriticalWeight = ons_rectDualPathSignedLoopObservable path ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.ons_rectDualPath_critical_defectKWDet_eq_signedLoopObservable embedding path


-- created on 2026-10-23
