import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part58
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailContractionExample


/--
[halfThirdScalingCertificate_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_c_eq_eq :
-- imply
  halfThirdScalingCertificate.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_c_eq

/--
[halfThirdScalingCertificate_mixed_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_mixed_lipschitz_eq
  {x y : FinitePlusTailState 1 ℕ} :
-- imply
  (halfThirdScalingCertificate.map x).dist (halfThirdScalingCertificate.map y) ≤ ((1 : ℝ) / 2) * x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_mixed_lipschitz x y

/--
[halfThirdScalingCertificate_c_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_c_lt_one_eq :
-- imply
  halfThirdScalingCertificate.c < 1 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_c_lt_one

/--
[halfThirdScalingBlockBounds_finite_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_finite_column_eq :
-- imply
  halfThirdScalingBlockBounds.finiteToFinite + halfThirdScalingBlockBounds.finiteToTail ≤ (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_finite_column

/--
[halfThirdScalingBlockBounds_tail_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_tail_column_eq :
-- imply
  halfThirdScalingBlockBounds.tailToFinite + halfThirdScalingBlockBounds.tailToTail ≤ (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_tail_column

/--
[halfThirdScalingFromBlockBoundsCertificate_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingFromBlockBoundsCertificate_c_eq_eq :
-- imply
  halfThirdScalingFromBlockBoundsCertificate.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingFromBlockBoundsCertificate_c_eq

/--
[halfThirdScalingBlockBounds_mixed_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_mixed_lipschitz_eq
  {x y : FinitePlusTailState 1 ℕ} :
-- imply
  (halfThirdScalingBlockBounds.map x).dist (halfThirdScalingBlockBounds.map y) ≤ ((1 : ℝ) / 2) * x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_mixed_lipschitz x y

/--
[zeroState_eq_ofFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroState_eq_ofFinite_eq :
-- imply
  zeroState = FinitePlusTailState.ofFinite (α := ℕ) (0 : Fin 1 → ℝ) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroState_eq_ofFinite

/--
[zeroFiniteClosedBallLift_center_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroFiniteClosedBallLift_center_eq_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  (zeroFiniteClosedBallLift hradius).center = zeroState := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroFiniteClosedBallLift_center_eq hradius

/--
[zeroFiniteClosedBallLift_exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroFiniteClosedBallLift_exists_fixedPoint_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  ∃ p : FinitePlusTailState 1 ℕ, (zeroFiniteClosedBallLift hradius).contraction.map p = p ∧ FinitePlusTailState.ClosedBall zeroState radius p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroFiniteClosedBallLift_exists_fixedPoint hradius

/--
[halfThirdScalingCertificate_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_map_zero_eq :
-- imply
  halfThirdScalingCertificate.map zeroState = zeroState := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_map_zero

/--
[halfThirdScalingCertificate_map_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_map_origin_eq :
-- imply
  halfThirdScalingCertificate.map (FinitePlusTailState.origin : FinitePlusTailState 1 ℕ) = FinitePlusTailState.origin := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_map_origin

/--
[halfThirdScalingBlockBounds_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_map_zero_eq :
-- imply
  halfThirdScalingBlockBounds.map zeroState = zeroState := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_map_zero

/--
[halfThirdScalingBlockBounds_map_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_map_origin_eq :
-- imply
  halfThirdScalingBlockBounds.map (FinitePlusTailState.origin : FinitePlusTailState 1 ℕ) = FinitePlusTailState.origin := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_map_origin

/--
[halfThirdScalingBlockBounds_zero_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_zero_residual_eq :
-- imply
  (halfThirdScalingBlockBounds.map zeroState).dist zeroState ≤ 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_zero_residual

/--
[halfThirdScalingBlockBounds_zero_finiteResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_zero_finiteResidual_eq :
-- imply
  FiniteContraction.l1Dist (halfThirdScalingBlockBounds.finiteMap zeroState) zeroState.finite ≤ 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_zero_finiteResidual

/--
[halfThirdScalingBlockBounds_zero_tailResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_zero_tailResidual_eq :
-- imply
  (halfThirdScalingBlockBounds.tailMap zeroState).dist zeroState.tail ≤ 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_zero_tailResidual

/--
[halfThirdScalingBlockBounds_zero_finiteResidual_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_zero_finiteResidual_mem_eq :
-- imply
  RatInterval.VectorMem (fun i => halfThirdScalingBlockBounds.finiteMap zeroState i - zeroState.finite i) halfThirdScalingBlockBoundsZeroFiniteResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_zero_finiteResidual_mem

/--
[halfThirdScalingBlockBounds_zero_finiteResidual_absSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_zero_finiteResidual_absSum_eq :
-- imply
  RatInterval.VectorAbsSum halfThirdScalingBlockBoundsZeroFiniteResidual = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_zero_finiteResidual_absSum

/--
[halfThirdScalingBlockBoundsComponentClosedBallCertificate_exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBoundsComponentClosedBallCertificate_exists_fixedPoint_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  ∃ p : FinitePlusTailState 1 ℕ, halfThirdScalingBlockBounds.map p = p ∧ FinitePlusTailState.ClosedBall zeroState radius p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBoundsComponentClosedBallCertificate_exists_fixedPoint hradius

/--
[halfThirdScalingBlockBoundsComponentClosedBallCertificate_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBoundsComponentClosedBallCertificate_fixedPoint_isFixed_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  halfThirdScalingBlockBounds.map (halfThirdScalingBlockBoundsComponentClosedBallCertificate hradius).fixedPoint = (halfThirdScalingBlockBoundsComponentClosedBallCertificate hradius).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBoundsComponentClosedBallCertificate_fixedPoint_isFixed hradius

/--
[halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate_fixedPoint_isFixed_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  halfThirdScalingBlockBounds.map (halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate hradius).fixedPoint = (halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate hradius).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate_fixedPoint_isFixed hradius

/--
[halfThirdScalingCertificate_iterate_mem_thermalStableCone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_iterate_mem_thermalStableCone_eq
  {thermal η t : ℝ}
  {s : FinitePlusTailState 1 ℕ}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hdom : ((1 : ℝ) / 2) ≤ |thermal|)
  (hs : FinitePlusTailState.ThermalStableCone η t s) :
-- imply
  FinitePlusTailState.ThermalStableCone η (thermal ^ k * t) (halfThirdScalingCertificate.iterate k s) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_iterate_mem_thermalStableCone hη hdom hs k

/--
[halfThirdScalingHyperbolicSplitting_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_cone_iterate_eq
  {η : ℝ}
  {x : FinitePlusTailHyperbolicSplitting.State 1 ℕ}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : halfThirdScalingHyperbolicSplitting.cone η x) :
-- imply
  halfThirdScalingHyperbolicSplitting.cone η (halfThirdScalingHyperbolicSplitting.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingHyperbolicSplitting_cone_iterate hη hx k

/--
[halfThirdScalingRGCertificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_fixedPointEnclosure_eq :
-- imply
  halfThirdScalingRGCertificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_fixedPointEnclosure

/--
[halfThirdScalingRGCertificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hyperbolicSplitting_eq :
-- imply
  halfThirdScalingRGCertificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hyperbolicSplitting

/--
[halfThirdScalingRGCertificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_linearizationEnclosure_eq :
-- imply
  halfThirdScalingRGCertificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_linearizationEnclosure

/--
[halfThirdScalingRGCertificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_predictedExponent_eq_eq :
-- imply
  halfThirdScalingRGCertificate.predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_predictedExponent_eq

/--
[halfThirdScalingRGCertificate_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_cone_iterate_eq
  {η : ℝ}
  {x : halfThirdScalingRGCertificate.H.carrier}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : halfThirdScalingHyperbolicSplitting.cone η x) :
-- imply
  halfThirdScalingHyperbolicSplitting.cone η (((halfThirdScalingRGCertificate.R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_cone_iterate hη hx k

/--
[halfThirdScalingRGCertificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : halfThirdScalingRGCertificate.RGToExponentBridge correlationLength) :
-- imply
  halfThirdScalingRGCertificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_of_bridge correlationLength hbridge

/--
[halfThirdScalingRGCertificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : halfThirdScalingRGCertificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_of_bridge correlationLength hbridge

/--
[halfThirdScalingRGCertificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingRGCertificate.predictedExponent) :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingRGCertificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingRGCertificate.predictedExponent) :
-- imply
  halfThirdScalingRGCertificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingCorrelationLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCorrelationLength_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), 0 < halfThirdScalingCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCorrelationLength_pos

/--
[halfThirdScalingCorrelationLength_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCorrelationLength_exact_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), halfThirdScalingCorrelationLength β = Real.exp (-halfThirdScalingRGCertificate.predictedExponent * Real.log (halfThirdScalingModel.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCorrelationLength_exact_power

/--
[halfThirdScalingToyRGCovariance_proof](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingToyRGCovariance_proof_eq :
-- imply
  halfThirdScalingToyRGCovariance := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingToyRGCovariance_proof

/--
[halfThirdScalingToyStableManifoldControl_proof](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingToyStableManifoldControl_proof_eq :
-- imply
  halfThirdScalingToyStableManifoldControl := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingToyStableManifoldControl_proof

/--
[halfThirdScalingToyMicroscopicOrbitEntry_proof](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingToyMicroscopicOrbitEntry_proof_eq :
-- imply
  halfThirdScalingToyMicroscopicOrbitEntry := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingToyMicroscopicOrbitEntry_proof

/--
[halfThirdScalingToySubcriticalMassBridge_proof](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingToySubcriticalMassBridge_proof_eq :
-- imply
  halfThirdScalingToySubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingToySubcriticalMassBridge_proof

/--
[halfThirdScalingRGCertificate_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_bridge_from_analyticInputs_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_bridge_from_analyticInputs

/--
[halfThirdScalingRGCertificate_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_from_analyticInputs_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_from_analyticInputs

/--
[halfThirdScalingRGCertificate_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_from_analyticInputs

/--
[halfThirdScalingPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingPrefactor_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), 0 < halfThirdScalingPrefactor β := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingPrefactor_pos

/--
[halfThirdScalingPrefactor_log_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingPrefactor_log_negligible_eq :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log (halfThirdScalingPrefactor β) / Real.log (halfThirdScalingModel.betaC - β)) (nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingPrefactor_log_negligible

/--
[halfThirdScalingDoublePrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingDoublePrefactor_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), 0 < halfThirdScalingDoublePrefactor β := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingDoublePrefactor_pos

/--
[halfThirdScalingDoublePrefactor_log_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingDoublePrefactor_log_negligible_eq :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log (halfThirdScalingDoublePrefactor β) / Real.log (halfThirdScalingModel.betaC - β)) (nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingDoublePrefactor_log_negligible

/--
[halfThirdScalingCorrelationLength_prefactor_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCorrelationLength_prefactor_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), halfThirdScalingCorrelationLength β = halfThirdScalingPrefactor β * Real.exp (-halfThirdScalingRGCertificate.predictedExponent * Real.log (halfThirdScalingModel.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCorrelationLength_prefactor_power

/--
[halfThirdScalingRGCertificate_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_bridge_from_prefactorInputs_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_bridge_from_prefactorInputs

/--
[halfThirdScalingRGCertificate_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_from_prefactorInputs_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_from_prefactorInputs

/--
[halfThirdScalingRGCertificate_valid_from_powerLawWrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_from_powerLawWrapper_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_from_powerLawWrapper

/--
[halfThirdScalingRGCertificate_hasCriticalNu_from_powerLawWrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_from_powerLawWrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_from_powerLawWrapper

/--
[halfThirdScalingRGCertificate_valid_from_prefactorTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_from_prefactorTransport_eq :
-- imply
  halfThirdScalingRGCertificate.Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_from_prefactorTransport

/--
[halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorTransport_eq :
-- imply
  HasCriticalNu halfThirdScalingModel (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorTransport

/--
[halfThirdScalingDoubleComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingDoubleComparison_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), (2 : ℝ) * halfThirdScalingCorrelationLength β ≤ halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β ∧ halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β ≤ (2 : ℝ) * halfThirdScalingCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingDoubleComparison

/--
[halfThirdScalingRGCertificate_valid_from_constantComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_from_constantComparison_eq :
-- imply
  halfThirdScalingRGCertificate.Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_from_constantComparison

/--
[halfThirdScalingRGCertificate_hasCriticalNu_from_constantComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_from_constantComparison_eq :
-- imply
  HasCriticalNu halfThirdScalingModel (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_from_constantComparison

/--
[halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs

/--
[halfThirdScalingMassPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingMassPrefactor_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), 0 < halfThirdScalingMassPrefactor β := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingMassPrefactor_pos

/--
[halfThirdScalingMassPrefactor_log_negligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingMassPrefactor_log_negligible_eq :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log (halfThirdScalingMassPrefactor β) / Real.log (halfThirdScalingModel.betaC - β)) (nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingMassPrefactor_log_negligible

/--
[halfThirdScalingMass_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingMass_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), halfThirdScalingMass β = halfThirdScalingMassPrefactor β * Real.exp (halfThirdScalingRGCertificate.predictedExponent * Real.log (halfThirdScalingModel.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingMass_power

/--
[halfThirdScalingCorrelationLength_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCorrelationLength_eq_inv_mass_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), halfThirdScalingCorrelationLength β = (halfThirdScalingMass β)⁻¹ := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCorrelationLength_eq_inv_mass

/--
[halfThirdScalingRGCertificate_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_bridge_from_massInputs_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_bridge_from_massInputs

/--
[halfThirdScalingRGCertificate_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_from_massInputs_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_from_massInputs

/--
[halfThirdScalingRGCertificate_valid_from_massPowerLawWrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_valid_from_massPowerLawWrapper_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_valid_from_massPowerLawWrapper

/--
[halfThirdScalingRGCertificate_hasCriticalNu_from_massPowerLawWrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_from_massPowerLawWrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_from_massPowerLawWrapper

/--
[halfThirdScalingRGCertificate_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRGCertificate_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRGCertificate_hasCriticalNu_from_massInputs

/--
[halfThirdScalingBlockRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_predictedExponent_eq_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_predictedExponent_eq

/--
[halfThirdScalingBlockRGPackage_relaxedC_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedC_c_eq :
-- imply
  halfThirdScalingBlockRGPackage_relaxedC.c = (3 : ℝ) / 4 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedC_c

/--
[halfThirdScalingBlockRGPackage_relaxedC_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedC_certificate_eq_eq :
-- imply
  halfThirdScalingBlockRGPackage_relaxedC.certificate halfThirdScalingBlockScale halfThirdScalingModel = halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedC_certificate_eq

/--
[halfThirdScalingBlockRGPackage_relaxedC_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedC_predictedExponent_eq_eq :
-- imply
  (halfThirdScalingBlockRGPackage_relaxedC.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedC_predictedExponent_eq

/--
[halfThirdScalingBlockRGPackage_relaxedC_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedC_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingBlockRGPackage_relaxedC.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedC_hasCriticalNu correlationLength hν

/--
[halfThirdScalingBlockRGPackage_relaxedConstants_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedConstants_c_eq :
-- imply
  halfThirdScalingBlockRGPackage_relaxedConstants.c = (3 : ℝ) / 4 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedConstants_c

/--
[halfThirdScalingBlockRGPackage_relaxedConstants_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedConstants_certificate_eq_eq :
-- imply
  halfThirdScalingBlockRGPackage_relaxedConstants.certificate halfThirdScalingBlockScale halfThirdScalingModel = halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedConstants_certificate_eq

/--
[halfThirdScalingBlockRGPackage_relaxedConstants_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedConstants_predictedExponent_eq_eq :
-- imply
  (halfThirdScalingBlockRGPackage_relaxedConstants.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedConstants_predictedExponent_eq

/--
[halfThirdScalingBlockRGPackage_relaxedConstants_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_relaxedConstants_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingBlockRGPackage_relaxedConstants.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGPackage_relaxedConstants_hasCriticalNu correlationLength hν

/--
[halfThirdScalingBlockRGCertificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_fixedPointEnclosure_eq :
-- imply
  halfThirdScalingBlockRGCertificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_fixedPointEnclosure

/--
[halfThirdScalingBlockRGCertificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_hyperbolicSplitting_eq :
-- imply
  halfThirdScalingBlockRGCertificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_hyperbolicSplitting

/--
[halfThirdScalingBlockRGCertificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_linearizationEnclosure_eq :
-- imply
  halfThirdScalingBlockRGCertificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_linearizationEnclosure

/--
[halfThirdScalingBlockRGCertificate_cone_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_cone_iterate_eq
  {η : ℝ}
  {x : halfThirdScalingBlockRGCertificate.H.carrier}
  {k : ℕ}
-- given
  (hη : 0 ≤ η)
  (hx : halfThirdScalingBlockRGPackage.hyperbolicSplitting.cone η x) :
-- imply
  halfThirdScalingBlockRGPackage.hyperbolicSplitting.cone η (((halfThirdScalingBlockRGCertificate.R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_cone_iterate hη hx k

/--
[halfThirdScalingBlockRGCertificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : halfThirdScalingBlockRGCertificate.RGToExponentBridge correlationLength) :
-- imply
  halfThirdScalingBlockRGCertificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_valid_of_bridge correlationLength hbridge

/--
[halfThirdScalingBlockRGCertificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : halfThirdScalingBlockRGCertificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingBlockRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_hasCriticalNu_of_bridge correlationLength hbridge

/--
[halfThirdScalingBlockRGCertificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingBlockRGCertificate.predictedExponent) :
-- imply
  halfThirdScalingBlockRGCertificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingBlockRGCertificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingBlockRGCertificate.predictedExponent) :
-- imply
  halfThirdScalingBlockRGCertificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_valid_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg_eq :
-- imply
  halfThirdScalingBlockRGCertificate.predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg

/--
[halfThirdScalingBlockRGCertificate_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_bridge_from_analyticInputs_eq :
-- imply
  halfThirdScalingBlockRGCertificate.RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_bridge_from_analyticInputs

/--
[halfThirdScalingBlockRGCertificate_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_valid_from_analyticInputs_eq :
-- imply
  halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_valid_from_analyticInputs

/--
[halfThirdScalingBlockRGCertificate_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingBlockRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_hasCriticalNu_from_analyticInputs

/--
[halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs_eq :
-- imply
  halfThirdScalingBlockRGCertificate.RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs

/--
[halfThirdScalingBlockRGCertificate_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_valid_from_prefactorInputs_eq :
-- imply
  halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_valid_from_prefactorInputs

/--
[halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingBlockRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs

/--
[halfThirdScalingBlockRGCertificate_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_bridge_from_massInputs_eq :
-- imply
  halfThirdScalingBlockRGCertificate.RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_bridge_from_massInputs

/--
[halfThirdScalingBlockRGCertificate_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_valid_from_massInputs_eq :
-- imply
  halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_valid_from_massInputs

/--
[halfThirdScalingBlockRGCertificate_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGCertificate_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength halfThirdScalingBlockRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockRGCertificate_hasCriticalNu_from_massInputs

/--
[halfThirdScalingCertificate_zero_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_zero_residual_eq :
-- imply
  (halfThirdScalingCertificate.map zeroState).dist zeroState ≤ 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_zero_residual

/--
[halfThirdScalingCertificate_unitCenter_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_unitCenter_residual_eq :
-- imply
  (halfThirdScalingCertificate.map unitCenterState).dist unitCenterState ≤ (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_unitCenter_residual

/--
[halfThirdScalingCertificate_fixedPoint_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_fixedPoint_eq_zero_eq :
-- imply
  halfThirdScalingCertificate.fixedPoint = zeroState := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_fixedPoint_eq_zero

/--
[halfThirdScalingCertificate_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_exists_unique_fixedPoint_eq :
-- imply
  ∃! p : FinitePlusTailState 1 ℕ, halfThirdScalingCertificate.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_exists_unique_fixedPoint

/--
[halfThirdScalingCertificate_mapsClosedBall_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_mapsClosedBall_zero_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  FinitePlusTailState.MapsClosedBall halfThirdScalingCertificate.map zeroState radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_mapsClosedBall_zero hradius

/--
[halfThirdScalingBlockBounds_mapsClosedBall_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBounds_mapsClosedBall_zero_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  FinitePlusTailState.MapsClosedBall halfThirdScalingBlockBounds.map zeroState radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBounds_mapsClosedBall_zero hradius

/--
[halfThirdScalingBlockBoundsClosedBallCertificate_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockBoundsClosedBallCertificate_fixedPoint_isFixed_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  halfThirdScalingBlockBounds.map (halfThirdScalingBlockBoundsClosedBallCertificate hradius).fixedPoint = (halfThirdScalingBlockBoundsClosedBallCertificate hradius).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingBlockBoundsClosedBallCertificate_fixedPoint_isFixed hradius

/--
[halfThirdScalingZeroClosedBallRGCertificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGCertificate_fixedPointEnclosure_eq :
-- imply
  halfThirdScalingZeroClosedBallRGCertificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGCertificate_fixedPointEnclosure

/--
[halfThirdScalingZeroClosedBallRGCertificate_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGCertificate_fixedPoint_mem_eq :
-- imply
  FinitePlusTailState.ClosedBall zeroState 1 halfThirdScalingZeroClosedBallRGCertificate.fixedPointData.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGCertificate_fixedPoint_mem

/--
[halfThirdScalingZeroClosedBallRGCertificate_iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGCertificate_iterate_mem_eq
  {x : halfThirdScalingZeroClosedBallRGCertificate.H.carrier}
  {k : ℕ}
-- given
  (hx : FinitePlusTailState.ClosedBall zeroState 1 x) :
-- imply
  FinitePlusTailState.ClosedBall zeroState 1 (((halfThirdScalingZeroClosedBallRGCertificate.R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGCertificate_iterate_mem hx k

/--
[halfThirdScalingZeroClosedBallRGPackage_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGPackage_fixedPoint_mem_eq :
-- imply
  FinitePlusTailState.ClosedBall halfThirdScalingZeroClosedBallRGPackage.closedBall.center halfThirdScalingZeroClosedBallRGPackage.closedBall.radius (halfThirdScalingZeroClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).fixedPointData.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGPackage_fixedPoint_mem

/--
[halfThirdScalingZeroClosedBallRGPackage_iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGPackage_iterate_mem_eq
  {x : (halfThirdScalingZeroClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).H.carrier}
  {k : ℕ}
-- given
  (hx : FinitePlusTailState.ClosedBall halfThirdScalingZeroClosedBallRGPackage.closedBall.center halfThirdScalingZeroClosedBallRGPackage.closedBall.radius x) :
-- imply
  FinitePlusTailState.ClosedBall halfThirdScalingZeroClosedBallRGPackage.closedBall.center halfThirdScalingZeroClosedBallRGPackage.closedBall.radius ((((halfThirdScalingZeroClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGPackage_iterate_mem hx k

/--
[halfThirdScalingZeroClosedBallRGPackage_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGPackage_thermalEigenvalue_eq_eq :
-- imply
  (halfThirdScalingZeroClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).thermalEigenvalue = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGPackage_thermalEigenvalue_eq

/--
[halfThirdScalingZeroClosedBallRGPackage_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGPackage_scale_eq_eq :
-- imply
  (halfThirdScalingZeroClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).scale = halfThirdScalingBlockScale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGPackage_scale_eq

/--
[halfThirdScalingZeroClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingZeroClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (halfThirdScalingZeroClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingZeroClosedBallRGPackage_predictedExponent_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_radius_eq_eq :
-- imply
  halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.closedBall.radius = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_radius_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_thermal_eq_eq :
-- imply
  halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_thermal_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_predictedExponent_eq_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_predictedExponent_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_hasCriticalNu correlationLength hν

/--
[halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_residual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_residual_eq_eq :
-- imply
  halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.closedBall.residual = (3 : ℝ) / 4 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_residual_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_predictedExponent_eq_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_predictedExponent_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_hasCriticalNu correlationLength hν

/--
[zeroTableClosedBallRGPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_tailTotalTsum_le_residual_eq :
-- imply
  zeroTableClosedBallRGPackage.tailTotalTsum ≤ zeroTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_tailTotalTsum_le_residual

/--
[zeroTableClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_predictedExponent_eq

/--
[generatedStableKeyEmptySupport_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyEmptySupport_saturated_eq :
-- imply
  ∀ a, classifyFiniteCutoffStableKey tableClosedBallCouplingCutoff a ∈ generatedStableKeyEmptySupport.image (classifyFiniteCutoffStableKey tableClosedBallCouplingCutoff) → a ∈ generatedStableKeyEmptySupport := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyEmptySupport_saturated

/--
[generatedStableKeyEmptyInfiniteTailPackage_budget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyEmptyInfiniteTailPackage_budget_eq_zero_eq :
-- imply
  generatedStableKeyEmptyInfiniteTailPackage.tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyEmptyInfiniteTailPackage_budget_eq_zero

/--
[generatedStableKeyTableClosedBallRGPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyTableClosedBallRGPackage_tailTotalTsum_le_residual_eq :
-- imply
  generatedStableKeyTableClosedBallRGPackage.tailTotalTsum ≤ generatedStableKeyTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyTableClosedBallRGPackage_tailTotalTsum_le_residual

/--
[generatedStableKeyTableClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyTableClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (generatedStableKeyTableClosedBallRGPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyTableClosedBallRGPackage_predictedExponent_eq

/--
[zeroTableClosedBallRGPackage_radiusFive_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_radiusFive_radius_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_radiusFive.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_radiusFive_radius_eq

/--
[zeroTableClosedBallRGPackage_radiusFive_residual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_radiusFive_residual_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_radiusFive.closedBallResidual = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_radiusFive_residual_eq

/--
[zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_radiusFive.closedBallContraction.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq

/--
[zeroTableClosedBallRGPackage_radiusFiveResidualTwo_residual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_radiusFiveResidualTwo_residual_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_radiusFiveResidualTwo.closedBallResidual = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_radiusFiveResidualTwo_residual_eq

/--
[zeroTableClosedBallRGPackage_radiusFiveResidualTwo_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_radiusFiveResidualTwo_thermal_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_radiusFiveResidualTwo.closedBallRG.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_radiusFiveResidualTwo_thermal_eq

/--
[zeroTableClosedBallRGPackage_replacedTableWitness_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitness_thermal_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitness.closedBallRG.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitness_thermal_eq

/--
[zeroTableClosedBallRGPackage_replacedTableWitness_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitness_budget_eq_two_eq :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitness.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitness_budget_eq_two

/--
[zeroTableClosedBallRGPackage_replacedTableWitness_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitness_certificate_eq_eq
  {scale : BlockScale} :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitness.certificate scale = zeroTableClosedBallRGPackage_radiusFiveResidualTwo.certificate scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitness_certificate_eq scale

/--
[zeroTableClosedBallRGPackage_replacedTableWitness_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitness_predictedExponent_eq_eq :
-- imply
  (zeroTableClosedBallRGPackage_replacedTableWitness.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitness_predictedExponent_eq

/--
[zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_residual_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_residual_eq_two_eq :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallResidual = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_residual_eq_two

/--
[zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_radius_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_radius_eq

/--
[zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_contraction_c_eq_eq :
-- imply
  (zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallContraction).c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_contraction_c_eq

/--
[zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_thermal_eq_eq :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallRG.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_thermal_eq

/--
[zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_budget_eq_two_eq :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_budget_eq_two

/--
[zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_certificate_eq_eq
  {scale : BlockScale} :
-- imply
  zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.certificate scale = zeroTableClosedBallRGPackage_radiusFive.certificate scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_certificate_eq scale

/--
[generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two_eq :
-- imply
  generatedStableKeyReplacedInfiniteTailPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_residual_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_residual_eq_two_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_residual_eq_two

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_thermal_eq_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRG.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_thermal_eq

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_radius_eq_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_radius_eq

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_contraction_c_eq_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_contraction_c_eq

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_two_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_two

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_residual_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound = generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_residual

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_le_residual_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum ≤ generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_le_residual

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_radius_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum + generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.c * generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius ≤ generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_radius

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_certificate_eq_eq
  {scale : BlockScale} :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.certificate scale = zeroTableClosedBallRGPackage_radiusFive.certificate scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_certificate_eq scale

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq

/--
[genMinCubicKeyEmptySupport_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyEmptySupport_saturated_eq :
-- imply
  ∀ a, classifyFiniteCutoffMinimalCubicStableKey tableClosedBallCouplingCutoff a ∈ genMinCubicKeyEmptySupport.image (classifyFiniteCutoffMinimalCubicStableKey tableClosedBallCouplingCutoff) → a ∈ genMinCubicKeyEmptySupport := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyEmptySupport_saturated

/--
[genMinCubicKeyEmptyInfiniteTailPackage_budget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyEmptyInfiniteTailPackage_budget_eq_zero_eq :
-- imply
  genMinCubicKeyEmptyInfiniteTailPackage.tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyEmptyInfiniteTailPackage_budget_eq_zero

/--
[genMinCubicKeyTableClosedBallRGPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyTableClosedBallRGPackage_tailTotalTsum_le_residual_eq :
-- imply
  genMinCubicKeyTableClosedBallRGPackage.tailTotalTsum ≤ genMinCubicKeyTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyTableClosedBallRGPackage_tailTotalTsum_le_residual

/--
[genMinCubicKeyTableClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyTableClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (genMinCubicKeyTableClosedBallRGPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyTableClosedBallRGPackage_predictedExponent_eq

/--
[genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two_eq :
-- imply
  genMinCubicKeyReplacedInfiniteTailPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_residual_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_residual_eq_two_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_residual_eq_two

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_thermal_eq_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRG.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_thermal_eq

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_radius_eq_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_radius_eq

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_contraction_c_eq_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_contraction_c_eq

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_two_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_two

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_residual_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound = genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_residual

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_le_residual_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum ≤ genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_le_residual

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_radius_eq :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum + genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.c * genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius ≤ genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_radius

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_certificate_eq_eq
  {scale : BlockScale} :
-- imply
  genMinCubicKeyReplacedTableClosedBallRGPackage.certificate scale = zeroTableClosedBallRGPackage_radiusFive.certificate scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_certificate_eq scale

/--
[genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq

/--
[genBoundedCaseEmptySupport_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseEmptySupport_saturated_eq :
-- imply
  ∀ a, classifyFiniteCutoffCoordinate tableClosedBallCouplingCutoff a ∈ genBoundedCaseEmptySupport.image (classifyFiniteCutoffCoordinate tableClosedBallCouplingCutoff) → a ∈ genBoundedCaseEmptySupport := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseEmptySupport_saturated

/--
[genBoundedCaseEmptyInfiniteTailPackage_budget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseEmptyInfiniteTailPackage_budget_eq_zero_eq :
-- imply
  genBoundedCaseEmptyInfiniteTailPackage.tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseEmptyInfiniteTailPackage_budget_eq_zero

/--
[genBoundedCaseTableClosedBallRGPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseTableClosedBallRGPackage_tailTotalTsum_le_residual_eq :
-- imply
  genBoundedCaseTableClosedBallRGPackage.tailTotalTsum ≤ genBoundedCaseTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseTableClosedBallRGPackage_tailTotalTsum_le_residual

/--
[genBoundedCaseTableClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseTableClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (genBoundedCaseTableClosedBallRGPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseTableClosedBallRGPackage_predictedExponent_eq

/--
[genCubicClassEmptySupport_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassEmptySupport_saturated_eq :
-- imply
  ∀ a, BoundedPolymerCase.classifyFiniteCutoffCubicClass tableClosedBallCouplingCutoff a ∈ genCubicClassEmptySupport.image (BoundedPolymerCase.classifyFiniteCutoffCubicClass tableClosedBallCouplingCutoff) → a ∈ genCubicClassEmptySupport := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassEmptySupport_saturated

/--
[genCubicClassEmptyInfiniteTailPackage_budget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassEmptyInfiniteTailPackage_budget_eq_zero_eq :
-- imply
  genCubicClassEmptyInfiniteTailPackage.tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassEmptyInfiniteTailPackage_budget_eq_zero

/--
[genCubicClassTableClosedBallRGPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassTableClosedBallRGPackage_tailTotalTsum_le_residual_eq :
-- imply
  genCubicClassTableClosedBallRGPackage.tailTotalTsum ≤ genCubicClassTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassTableClosedBallRGPackage_tailTotalTsum_le_residual

/--
[genCubicClassTableClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassTableClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (genCubicClassTableClosedBallRGPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassTableClosedBallRGPackage_predictedExponent_eq

/--
[genBoundedCaseRadiusFive_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseRadiusFive_radius_eq_eq :
-- imply
  genBoundedCaseRadiusFive.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseRadiusFive_radius_eq

/--
[genBoundedCaseRadiusFive_residual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseRadiusFive_residual_eq_eq :
-- imply
  genBoundedCaseRadiusFive.closedBallResidual = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseRadiusFive_residual_eq

/--
[genBoundedCaseRadiusFive_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseRadiusFive_contraction_c_eq_eq :
-- imply
  genBoundedCaseRadiusFive.closedBallContraction.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseRadiusFive_contraction_c_eq

/--
[genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two_eq :
-- imply
  genBoundedCaseReplacedInfiniteTailPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two

/--
[genBoundedCaseReplacedPackage_residual_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_residual_eq_two_eq :
-- imply
  genBoundedCaseReplacedPackage.closedBallResidual = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_residual_eq_two

/--
[genBoundedCaseReplacedPackage_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_thermal_eq_eq :
-- imply
  genBoundedCaseReplacedPackage.closedBallRG.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_thermal_eq

/--
[genBoundedCaseReplacedPackage_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_radius_eq_eq :
-- imply
  genBoundedCaseReplacedPackage.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_radius_eq

/--
[genBoundedCaseReplacedPackage_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_contraction_c_eq_eq :
-- imply
  genBoundedCaseReplacedPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_contraction_c_eq

/--
[genBoundedCaseReplacedPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_budget_eq_two_eq :
-- imply
  genBoundedCaseReplacedPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_budget_eq_two

/--
[genBoundedCaseReplacedPackage_budget_eq_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_budget_eq_residual_eq :
-- imply
  genBoundedCaseReplacedPackage.tableCertifiedTotalBound = genBoundedCaseReplacedPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_budget_eq_residual

/--
[genBoundedCaseReplacedPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_tailTotalTsum_le_residual_eq :
-- imply
  genBoundedCaseReplacedPackage.tailTotalTsum ≤ genBoundedCaseReplacedPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_tailTotalTsum_le_residual

/--
[genBoundedCaseReplacedPackage_tailTotalTsum_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_tailTotalTsum_radius_eq :
-- imply
  genBoundedCaseReplacedPackage.tailTotalTsum + genBoundedCaseReplacedPackage.closedBallContraction.c * genBoundedCaseReplacedPackage.closedBallRadius ≤ genBoundedCaseReplacedPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_tailTotalTsum_radius

/--
[genBoundedCaseReplacedPackage_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_certificate_eq_eq
  {scale : BlockScale} :
-- imply
  genBoundedCaseReplacedPackage.certificate scale = genBoundedCaseRadiusFive.certificate scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_certificate_eq scale

/--
[genBoundedCaseReplacedPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_predictedExponent_eq_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genBoundedCaseReplacedPackage_predictedExponent_eq

/--
[genCubicClassRadiusFive_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassRadiusFive_radius_eq_eq :
-- imply
  genCubicClassRadiusFive.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassRadiusFive_radius_eq

/--
[genCubicClassRadiusFive_residual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassRadiusFive_residual_eq_eq :
-- imply
  genCubicClassRadiusFive.closedBallResidual = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassRadiusFive_residual_eq

/--
[genCubicClassRadiusFive_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassRadiusFive_contraction_c_eq_eq :
-- imply
  genCubicClassRadiusFive.closedBallContraction.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassRadiusFive_contraction_c_eq

/--
[genCubicClassReplacedInfiniteTailPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedInfiniteTailPackage_budget_eq_two_eq :
-- imply
  genCubicClassReplacedInfiniteTailPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedInfiniteTailPackage_budget_eq_two

/--
[genCubicClassReplacedPackage_residual_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_residual_eq_two_eq :
-- imply
  genCubicClassReplacedPackage.closedBallResidual = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_residual_eq_two

/--
[genCubicClassReplacedPackage_thermal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_thermal_eq_eq :
-- imply
  genCubicClassReplacedPackage.closedBallRG.thermal = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_thermal_eq

/--
[genCubicClassReplacedPackage_radius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_radius_eq_eq :
-- imply
  genCubicClassReplacedPackage.closedBallRadius = 5 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_radius_eq

/--
[genCubicClassReplacedPackage_contraction_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_contraction_c_eq_eq :
-- imply
  genCubicClassReplacedPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_contraction_c_eq

/--
[genCubicClassReplacedPackage_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_budget_eq_two_eq :
-- imply
  genCubicClassReplacedPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_budget_eq_two

/--
[genCubicClassReplacedPackage_budget_eq_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_budget_eq_residual_eq :
-- imply
  genCubicClassReplacedPackage.tableCertifiedTotalBound = genCubicClassReplacedPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_budget_eq_residual

/--
[genCubicClassReplacedPackage_tailTotalTsum_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_tailTotalTsum_le_residual_eq :
-- imply
  genCubicClassReplacedPackage.tailTotalTsum ≤ genCubicClassReplacedPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_tailTotalTsum_le_residual

/--
[genCubicClassReplacedPackage_tailTotalTsum_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_tailTotalTsum_radius_eq :
-- imply
  genCubicClassReplacedPackage.tailTotalTsum + genCubicClassReplacedPackage.closedBallContraction.c * genCubicClassReplacedPackage.closedBallRadius ≤ genCubicClassReplacedPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_tailTotalTsum_radius

/--
[genCubicClassReplacedPackage_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_certificate_eq_eq
  {scale : BlockScale} :
-- imply
  genCubicClassReplacedPackage.certificate scale = genCubicClassRadiusFive.certificate scale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_certificate_eq scale

/--
[genCubicClassReplacedPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_predictedExponent_eq_eq :
-- imply
  (genCubicClassReplacedPackage.certificate FiniteWitnessPackageExample.exampleScale).predictedExponent = predictedNu FiniteWitnessPackageExample.exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.genCubicClassReplacedPackage_predictedExponent_eq

/--
[halfThirdScalingUnitClosedBallRGCertificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGCertificate_fixedPointEnclosure_eq :
-- imply
  halfThirdScalingUnitClosedBallRGCertificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGCertificate_fixedPointEnclosure

/--
[halfThirdScalingUnitClosedBallRGPackage_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_thermalEigenvalue_eq_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).thermalEigenvalue = 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_thermalEigenvalue_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_scale_eq_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).scale = halfThirdScalingBlockScale := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_scale_eq

/--
[halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = predictedNu halfThirdScalingBlockScale 3 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq

/--
[halfThirdScalingUnitClosedBallRGCertificate_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGCertificate_fixedPoint_mem_eq :
-- imply
  FinitePlusTailState.ClosedBall unitCenterState 1 halfThirdScalingUnitClosedBallRGCertificate.fixedPointData.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGCertificate_fixedPoint_mem

/--
[halfThirdScalingUnitClosedBallRGCertificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGCertificate_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge correlationLength) :
-- imply
  halfThirdScalingUnitClosedBallRGCertificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGCertificate_valid_of_bridge correlationLength hbridge

/--
[halfThirdScalingUnitClosedBallRGCertificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGCertificate_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingUnitClosedBallRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGCertificate_hasCriticalNu_of_bridge correlationLength hbridge

/--
[halfThirdScalingUnitClosedBallRGCertificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGCertificate_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingUnitClosedBallRGCertificate.predictedExponent) :
-- imply
  halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGCertificate_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingUnitClosedBallRGCertificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGCertificate_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength halfThirdScalingUnitClosedBallRGCertificate.predictedExponent) :
-- imply
  halfThirdScalingUnitClosedBallRGCertificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGCertificate_valid_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingUnitClosedBallRGPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge correlationLength) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_valid_of_bridge correlationLength hbridge

/--
[halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_of_bridge correlationLength hbridge

/--
[halfThirdScalingUnitClosedBallRGPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingUnitClosedBallRGPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu halfThirdScalingModel correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallRGPackage_valid_of_hasCriticalNu correlationLength hν

/--
[halfThirdScalingClosedBallCertificate_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBallCertificate_mapsClosedBall_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  FinitePlusTailState.MapsClosedBall halfThirdScalingCertificate.map zeroState radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingClosedBallCertificate_mapsClosedBall hradius

/--
[halfThirdScalingClosedBallCertificate_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBallCertificate_fixedPoint_mem_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  FinitePlusTailState.ClosedBall zeroState radius halfThirdScalingCertificate.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingClosedBallCertificate_fixedPoint_mem hradius

/--
[halfThirdScalingClosedBallCertificate_exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBallCertificate_exists_fixedPoint_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  ∃ p : FinitePlusTailState 1 ℕ, halfThirdScalingCertificate.map p = p ∧ FinitePlusTailState.ClosedBall zeroState radius p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingClosedBallCertificate_exists_fixedPoint hradius

/--
[halfThirdScalingCertificate_iterate_contracts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_iterate_contracts_eq
  {k : ℕ}
  {x y : FinitePlusTailState 1 ℕ} :
-- imply
  (halfThirdScalingCertificate.iterate k x).dist (halfThirdScalingCertificate.iterate k y) ≤ ((1 : ℝ) / 2) ^ k * x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_iterate_contracts k x y

/--
[halfThirdScalingCertificate_iterate_contracts_to_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_iterate_contracts_to_fixedPoint_eq
  {k : ℕ}
  {x : FinitePlusTailState 1 ℕ} :
-- imply
  (halfThirdScalingCertificate.iterate k x).dist halfThirdScalingCertificate.fixedPoint ≤ ((1 : ℝ) / 2) ^ k * x.dist halfThirdScalingCertificate.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_iterate_contracts_to_fixedPoint k x

/--
[halfThirdScalingCertificate_iterate_mem_zero_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingCertificate_iterate_mem_zero_closedBall_eq
  {radius : ℝ}
  {x : FinitePlusTailState 1 ℕ}
  {k : ℕ}
-- given
  (hradius : 0 ≤ radius)
  (hx : FinitePlusTailState.ClosedBall zeroState radius x) :
-- imply
  FinitePlusTailState.ClosedBall zeroState radius (halfThirdScalingCertificate.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingCertificate_iterate_mem_zero_closedBall hradius hx k

/--
[halfThirdScalingClosedBallCertificate_iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBallCertificate_iterate_mem_eq
  {radius : ℝ}
  {x : FinitePlusTailState 1 ℕ}
  {k : ℕ}
-- given
  (hradius : 0 ≤ radius)
  (hx : FinitePlusTailState.ClosedBall zeroState radius x) :
-- imply
  FinitePlusTailState.ClosedBall zeroState radius (halfThirdScalingCertificate.iterate k x) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingClosedBallCertificate_iterate_mem hradius hx k

/--
[halfThirdScalingClosedBallCertificate_fixedPoint_mem_larger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBallCertificate_fixedPoint_mem_larger_eq
  {radius radius' : ℝ}
-- given
  (hradius : 0 ≤ radius)
  (hle : radius ≤ radius') :
-- imply
  FinitePlusTailState.ClosedBall zeroState radius' halfThirdScalingCertificate.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingClosedBallCertificate_fixedPoint_mem_larger hradius hle

/--
[halfThirdScalingRadiusOneFromZero_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingRadiusOneFromZero_fixedPoint_mem_eq :
-- imply
  FinitePlusTailState.ClosedBall zeroState 1 halfThirdScalingCertificate.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingRadiusOneFromZero_fixedPoint_mem

/--
[halfThirdScalingUnitClosedBallCertificate_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallCertificate_fixedPoint_mem_eq :
-- imply
  FinitePlusTailState.ClosedBall unitCenterState 1 halfThirdScalingCertificate.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.halfThirdScalingUnitClosedBallCertificate_fixedPoint_mem

/--
[zeroFiniteBlockTailHalfCertificate_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroFiniteBlockTailHalfCertificate_c_eq_eq :
-- imply
  zeroFiniteBlockTailHalfCertificate.c = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroFiniteBlockTailHalfCertificate_c_eq

/--
[zeroFiniteBlockTailHalfCertificate_mixed_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroFiniteBlockTailHalfCertificate_mixed_lipschitz_eq
  {x y : FinitePlusTailState 1 ℕ} :
-- imply
  (zeroFiniteBlockTailHalfCertificate.map x).dist (zeroFiniteBlockTailHalfCertificate.map y) ≤ ((1 : ℝ) / 2) * x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroFiniteBlockTailHalfCertificate_mixed_lipschitz x y

/--
[zeroFiniteBlockTailHalfCertificate_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroFiniteBlockTailHalfCertificate_map_zero_eq :
-- imply
  zeroFiniteBlockTailHalfCertificate.map zeroState = zeroState := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroFiniteBlockTailHalfCertificate_map_zero

/--
[zeroFiniteBlockTailHalfClosedBallCertificate_exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean)
-/
@[path]
private lemma zeroFiniteBlockTailHalfClosedBallCertificate_exists_fixedPoint_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  ∃ p : FinitePlusTailState 1 ℕ, zeroFiniteBlockTailHalfCertificate.map p = p ∧ FinitePlusTailState.ClosedBall zeroState radius p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailContractionExample.zeroFiniteBlockTailHalfClosedBallCertificate_exists_fixedPoint hradius


-- created on 2026-10-23
