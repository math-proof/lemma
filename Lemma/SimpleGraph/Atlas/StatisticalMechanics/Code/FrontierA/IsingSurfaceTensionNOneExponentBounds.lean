import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneExponentBounds
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[layerDotInt_ge_neg_nine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma layerDotInt_ge_neg_nine_eq
  {s t : Nat} :
-- imply
  -9 ≤ layerDotInt s t := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerDotInt_ge_neg_nine s t

/--
[layerLateralInt_ge_neg_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma layerLateralInt_ge_neg_sixteen_eq :
-- imply
  ∀ s : Fin 512, -16 ≤ layerLateralInt s := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerLateralInt_ge_neg_sixteen

/--
[layerEndpointInt_ge_neg_seventeen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma layerEndpointInt_ge_neg_seventeen_eq :
-- imply
  ∀ q : Fin 512, -17 ≤ layerLateralInt q + layerFaceInt q := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerEndpointInt_ge_neg_seventeen

/--
[layerLateral_halfShift_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma layerLateral_halfShift_nonneg_eq
  {s : Fin 512} :
-- imply
  0 ≤ halfShift (layerLateralInt s) 16 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerLateral_halfShift_nonneg s

/--
[layerEndpoint_halfShift_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma layerEndpoint_halfShift_nonneg_eq
  {q : Fin 512} :
-- imply
  0 ≤ halfShift (layerLateralInt q + layerFaceInt q) 17 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerEndpoint_halfShift_nonneg q

/--
[layerSeam_halfShift_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma layerSeam_halfShift_nonneg_eq
  {s q : Fin 512} :
-- imply
  0 ≤ halfShift (layerDotInt s q) 9 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerSeam_halfShift_nonneg s q

/--
[layerMiddle_halfShift_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma layerMiddle_halfShift_nonneg_eq
  {s v : Fin 512} :
-- imply
  0 ≤ halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerMiddle_halfShift_nonneg s v

/--
[BiPoly.eval_rawMomentPoly_eq_list_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma eval_rawMomentPoly_eq_list_stateSum_eq
  {X Y : Real}
-- given
  (hX : X ≠ 0) :
-- imply
  rawMomentPoly.eval X Y = ((List.range 512).map fun s => X ^ halfShift (layerLateralInt s) 16 * ((List.range 512).map fun v => X ^ halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26).sum * ((List.range 512).map fun q => X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 * Y ^ halfShift (layerDotInt s q) 9).sum).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_rawMomentPoly_eq_list_stateSum X Y hX

/--
[BiPoly.eval_rawMomentPoly_eq_fin_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneExponentBounds.lean)
-/
@[path]
private lemma eval_rawMomentPoly_eq_fin_stateSum_eq
  {X Y : Real}
-- given
  (hX : X ≠ 0) :
-- imply
  rawMomentPoly.eval X Y = ∑ s : Fin 512, X ^ halfShift (layerLateralInt s) 16 * (∑ v : Fin 512, X ^ halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) * (∑ q : Fin 512, X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 * Y ^ halfShift (layerDotInt s q) 9) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_rawMomentPoly_eq_fin_stateSum X Y hX


-- created on 2026-10-23
