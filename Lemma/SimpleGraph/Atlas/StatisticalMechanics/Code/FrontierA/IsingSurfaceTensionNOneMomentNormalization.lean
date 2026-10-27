import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneMomentNormalization.Part2
open Finset StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[BiPoly.eval_sumCodes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma eval_sumCodes_eq
  {X Y : Real}
-- given
  (f : Nat -> BiPoly) :
-- imply
  (BiPoly.sumCodes f).eval X Y = ((List.range 512).map fun s => (f s).eval X Y).sum := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_sumCodes X Y f

/--
[BiPoly.eval_sumCodes_eq_fin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma eval_sumCodes_eq_fin_sum_eq
  {X Y : Real}
-- given
  (f : Nat -> BiPoly) :
-- imply
  (BiPoly.sumCodes f).eval X Y = ∑ s : Fin 512, (f s).eval X Y := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_sumCodes_eq_fin_sum X Y f

/--
[layerLateralInt_halfShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma layerLateralInt_halfShift_eq
  {s : Fin 512} :
-- imply
  2 * halfShift (layerLateralInt s) 16 = layerLateralInt s + 16 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerLateralInt_halfShift s

/--
[layerEndpointInt_halfShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma layerEndpointInt_halfShift_eq
  {q : Fin 512} :
-- imply
  2 * halfShift (layerLateralInt q + layerFaceInt q) 17 = layerLateralInt q + layerFaceInt q + 17 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerEndpointInt_halfShift q

/--
[layerSeamInt_halfShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma layerSeamInt_halfShift_eq
  {s q : Fin 512} :
-- imply
  2 * halfShift (layerDotInt s q) 9 = layerDotInt s q + 9 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerSeamInt_halfShift s q

/--
[layerMiddleInt_halfShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma layerMiddleInt_halfShift_eq
  {s v : Fin 512} :
-- imply
  2 * halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 = layerDotInt s v + layerLateralInt v + layerFaceInt v + 26 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.layerMiddleInt_halfShift s v

/--
[eval_rawMomentPolyStateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma eval_rawMomentPolyStateSum_eq
  {X Y : Real}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  rawMomentPolyStateSum.eval X Y = ∑ s : Fin 512, X ^ halfShift (layerLateralInt s) 16 * (∑ v : Fin 512, X ^ halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) * (∑ q : Fin 512, X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 * Y ^ halfShift (layerDotInt s q) 9) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.eval_rawMomentPolyStateSum X Y hX hY

/--
[BiPoly.hasDerivAt_normalizedSeamEval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma hasDerivAt_normalizedSeamEval_eq
  {X r : Real}
  {p : BiPoly} :
-- imply
  HasDerivAt (fun u => Real.exp (-9 * u) * p.eval X (Real.exp (2 * u))) (Real.exp (-9 * r) * (p.scaleObservable 1).eval X (Real.exp (2 * r))) r := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.hasDerivAt_normalizedSeamEval X r p

/--
[BiPoly.hasDerivAt_normalizedSeamFirstEval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma hasDerivAt_normalizedSeamFirstEval_eq
  {X r : Real}
  {p : BiPoly} :
-- imply
  HasDerivAt (fun u => Real.exp (-9 * u) * (p.scaleObservable 1).eval X (Real.exp (2 * u))) (Real.exp (-9 * r) * (p.scaleObservable 2).eval X (Real.exp (2 * r))) r := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.hasDerivAt_normalizedSeamFirstEval X r p

/--
[exp_nOneWeight_eq_normalizedMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma exp_nOneWeight_eq_normalizedMonomial_eq
  {beta r : Real}
  {s v q : Fin 512} :
-- imply
  Real.exp (beta * ((layerLateralInt s : Real) + layerDotInt s v + layerLateralInt v + layerFaceInt v + layerLateralInt q + layerFaceInt q) + r * (layerDotInt s q : Real)) = Real.exp (-59 * beta - 9 * r) * Real.exp (2 * beta) ^ halfShift (layerLateralInt s) 16 * Real.exp (2 * beta) ^ halfShift (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 * Real.exp (2 * beta) ^ halfShift (layerLateralInt q + layerFaceInt q) 17 * Real.exp (2 * r) ^ halfShift (layerDotInt s q) 9 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.exp_nOneWeight_eq_normalizedMonomial beta r s v q

/--
[nOneTransferBridgeRawMomentCodeSum_eq_eval_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma nOneTransferBridgeRawMomentCodeSum_eq_eval_stateSum_eq
  {beta r : Real} :
-- imply
  nOneTransferBridgeRawMomentCodeSum beta r = Real.exp (-59 * beta - 9 * r) * rawMomentPolyStateSum.eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.nOneTransferBridgeRawMomentCodeSum_eq_eval_stateSum beta r

/--
[oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta 1 r = Real.exp (-59 * beta - 9 * r) * rawMomentPolyStateSum.eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum beta r

/--
[oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeRawFirst beta 1 r = Real.exp (-59 * beta - 9 * r) * (rawMomentPolyStateSum.scaleObservable 1).eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum beta r

/--
[oddPrismTransferBridgeRawSecond_one_eq_eval_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawSecond_one_eq_eval_stateSum_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeRawSecond beta 1 r = Real.exp (-59 * beta - 9 * r) * (rawMomentPolyStateSum.scaleObservable 2).eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeRawSecond_one_eq_eval_stateSum beta r

/--
[BiPoly.eval_varianceNumeratorPolyOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma eval_varianceNumeratorPolyOf_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  (varianceNumeratorPolyOf p).eval X Y = (p.scaleObservable 2).eval X Y * p.eval X Y - (p.scaleObservable 1).eval X Y ^ 2 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_varianceNumeratorPolyOf p X Y hX hY

/--
[BiPoly.eval_reflectedVarianceSkewPolyOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma eval_reflectedVarianceSkewPolyOf_eq
  {p : BiPoly}
  {X Y : Real}
-- given
  (hX : X ≠ 0)
  (hY : Y ≠ 0) :
-- imply
  (reflectedVarianceSkewPolyOf p).eval X Y = (varianceNumeratorPolyOf p).eval X Y * p.eval X Y⁻¹ ^ 2 - (varianceNumeratorPolyOf p).eval X Y⁻¹ * p.eval X Y ^ 2 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.BiPoly.eval_reflectedVarianceSkewPolyOf p X Y hX hY

/--
[oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeVarianceNumerator beta 1 r = Real.exp (-59 * beta - 9 * r) ^ 2 * (varianceNumeratorPolyOf rawMomentPolyStateSum).eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum beta r

/--
[oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_stateSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_stateSum_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeVarianceSkewNumerator beta 1 r = (Real.exp (-59 * beta - 9 * r) * Real.exp (-59 * beta + 9 * r)) ^ 2 * (reflectedVarianceSkewPolyOf rawMomentPolyStateSum).eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_stateSum beta r

/--
[nOneTransferBridgeRawMomentCodeSum_eq_eval_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma nOneTransferBridgeRawMomentCodeSum_eq_eval_rawMomentPoly_eq
  {beta r : Real} :
-- imply
  nOneTransferBridgeRawMomentCodeSum beta r = Real.exp (-59 * beta - 9 * r) * rawMomentPoly.eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.nOneTransferBridgeRawMomentCodeSum_eq_eval_rawMomentPoly beta r

/--
[oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeRawMoment beta 1 r = Real.exp (-59 * beta - 9 * r) * rawMomentPoly.eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly beta r

/--
[oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeRawFirst beta 1 r = Real.exp (-59 * beta - 9 * r) * (rawMomentPoly.scaleObservable 1).eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly beta r

/--
[oddPrismTransferBridgeRawSecond_one_eq_eval_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeRawSecond_one_eq_eval_rawMomentPoly_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeRawSecond beta 1 r = Real.exp (-59 * beta - 9 * r) * (rawMomentPoly.scaleObservable 2).eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeRawSecond_one_eq_eval_rawMomentPoly beta r

/--
[oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeVarianceNumerator beta 1 r = Real.exp (-59 * beta - 9 * r) ^ 2 * varianceNumeratorPoly.eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly beta r

/--
[oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_rawMomentPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_rawMomentPoly_eq
  {beta r : Real} :
-- imply
  oddPrismTransferBridgeVarianceSkewNumerator beta 1 r = (Real.exp (-59 * beta - 9 * r) * Real.exp (-59 * beta + 9 * r)) ^ 2 * reflectedVarianceSkewPoly.eval (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_rawMomentPoly beta r


-- created on 2026-10-23
