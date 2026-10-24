import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode
open Finset StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[nOneLayerCodeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma nOneLayerCodeEquiv_apply_eq
  {s : Fin 512}
  {p : Fin 3 × Fin 3} :
-- imply
  nOneLayerCodeEquiv s p = layerCodeBit s p := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.nOneLayerCodeEquiv_apply s p

/--
[spin_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma spin_nOneLayerCodeEquiv_eq
  {s : Fin 512}
  {p : Fin 3 × Fin 3} :
-- imply
  spin (nOneLayerCodeEquiv s) p = (spinInt s p : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.spin_nOneLayerCodeEquiv s p

/--
[sum_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma sum_nOneLayerCodeEquiv_eq
-- given
  (f : RectangularLayerConfig 3 3 -> Real) :
-- imply
  (∑ s : Fin 512, f (nOneLayerCodeEquiv s)) = ∑ s, f s := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.sum_nOneLayerCodeEquiv f

/--
[rectangularLayerInternalInteraction_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma rectangularLayerInternalInteraction_nOneLayerCodeEquiv_eq
  {s : Fin 512} :
-- imply
  rectangularLayerInternalInteraction (nOneLayerCodeEquiv s) = (layerInternalInt s : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rectangularLayerInternalInteraction_nOneLayerCodeEquiv s

/--
[rectangularLayerLateralInteraction_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma rectangularLayerLateralInteraction_nOneLayerCodeEquiv_eq
  {s : Fin 512} :
-- imply
  rectangularLayerInternalInteraction (nOneLayerCodeEquiv s) + ∑ p : Fin 3 × Fin 3, rectangularLayerBoundaryDegree p * spin (nOneLayerCodeEquiv s) p = (layerLateralInt s : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rectangularLayerLateralInteraction_nOneLayerCodeEquiv s

/--
[rectangularLayerFaceInteraction_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma rectangularLayerFaceInteraction_nOneLayerCodeEquiv_eq
  {s : Fin 512} :
-- imply
  (∑ p : Fin 3 × Fin 3, spin (nOneLayerCodeEquiv s) p) = (layerFaceInt s : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rectangularLayerFaceInteraction_nOneLayerCodeEquiv s

/--
[rectangularLayerSeamInteraction_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma rectangularLayerSeamInteraction_nOneLayerCodeEquiv_eq
  {s t : Fin 512} :
-- imply
  oddPrismLayerSeamInteraction 1 (nOneLayerCodeEquiv s) (nOneLayerCodeEquiv t) = (layerDotInt s t : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rectangularLayerSeamInteraction_nOneLayerCodeEquiv s t

/--
[rectangularLayerBoltzmannInteraction_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma rectangularLayerBoltzmannInteraction_nOneLayerCodeEquiv_eq
  {beta : Real}
  {s : Fin 512} :
-- imply
  rectangularLayerBoltzmannInteraction 1 beta (nOneLayerCodeEquiv s) = beta * (layerLateralInt s : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rectangularLayerBoltzmannInteraction_nOneLayerCodeEquiv beta s

/--
[rectangularLayerFaceBoundary_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma rectangularLayerFaceBoundary_nOneLayerCodeEquiv_eq
  {beta : Real}
  {s : Fin 512} :
-- imply
  rectangularLayerFaceBoundary 1 beta (nOneLayerCodeEquiv s) = beta * (layerFaceInt s : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rectangularLayerFaceBoundary_nOneLayerCodeEquiv beta s

/--
[rectangularLayerVerticalInteraction_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma rectangularLayerVerticalInteraction_nOneLayerCodeEquiv_eq
  {beta : Real}
  {s t : Fin 512} :
-- imply
  rectangularLayerVerticalInteraction 1 beta (nOneLayerCodeEquiv s) (nOneLayerCodeEquiv t) = beta * (layerDotInt s t : Real) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.rectangularLayerVerticalInteraction_nOneLayerCodeEquiv beta s t

/--
[oddPrismUpperConditionedVector_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma oddPrismUpperConditionedVector_nOneLayerCodeEquiv_eq
  {beta : Real}
  {q : Fin 512} :
-- imply
  oddPrismUpperConditionedVector beta 1 (nOneLayerCodeEquiv q) = Real.exp (beta * ((layerLateralInt q : Real) + layerFaceInt q)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismUpperConditionedVector_nOneLayerCodeEquiv beta q

/--
[oddPrismLowerConditionedVector_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma oddPrismLowerConditionedVector_nOneLayerCodeEquiv_eq
  {beta : Real}
  {s : Fin 512} :
-- imply
  oddPrismLowerConditionedVector beta 1 (nOneLayerCodeEquiv s) = ∑ v : Fin 512, Real.exp (beta * ((layerLateralInt s : Real) + layerDotInt s v + layerLateralInt v + layerFaceInt v)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismLowerConditionedVector_nOneLayerCodeEquiv beta s

/--
[oddPrismPureSeamKernel_nOneLayerCodeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma oddPrismPureSeamKernel_nOneLayerCodeEquiv_eq
  {r : Real}
  {s q : Fin 512} :
-- imply
  oddPrismPureSeamKernel r 1 (nOneLayerCodeEquiv s) (nOneLayerCodeEquiv q) = Real.exp (r * (layerDotInt s q : Real)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismPureSeamKernel_nOneLayerCodeEquiv r s q

/--
[oddPrismTransferBridgeRawMoment_one_eq_codeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_one_eq_codeSum_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta 1 r = nOneTransferBridgeRawMomentCodeSum beta r := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeRawMoment_one_eq_codeSum beta r


-- created on 2026-10-23
