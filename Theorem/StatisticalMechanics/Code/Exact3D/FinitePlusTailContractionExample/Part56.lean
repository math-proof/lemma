/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part57


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingUnitClosedBallRGCertificate_fixedPointEnclosure :
    halfThirdScalingUnitClosedBallRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_fixedPointEnclosure
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)


theorem halfThirdScalingUnitClosedBallRGPackage_thermalEigenvalue_eq :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).thermalEigenvalue =
        3 :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_thermalEigenvalue_eq
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingUnitClosedBallRGPackage_scale_eq :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).scale =
        halfThirdScalingBlockScale :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_scale_eq
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingUnitClosedBallRGCertificate_fixedPoint_mem :
    FinitePlusTailState.ClosedBall unitCenterState 1
      halfThirdScalingUnitClosedBallRGCertificate.fixedPointData.fixedPoint := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate,
    halfThirdScalingUnitClosedBallCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_fixedPoint_mem_closedBall
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)


theorem halfThirdScalingUnitClosedBallRGCertificate_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge
        correlationLength) :
    halfThirdScalingUnitClosedBallRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_valid_of_bridge
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)
      correlationLength hbridge


theorem halfThirdScalingUnitClosedBallRGCertificate_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      halfThirdScalingUnitClosedBallRGCertificate.predictedExponent :=
  (halfThirdScalingUnitClosedBallRGCertificate_valid_of_bridge
    correlationLength hbridge).hasCriticalNu


theorem
    halfThirdScalingUnitClosedBallRGCertificate_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingUnitClosedBallRGCertificate.predictedExponent) :
    halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge
      correlationLength := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_rgToExponentBridge_of_hasCriticalNu
      halfThirdScalingUnitClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)
      correlationLength hν


theorem halfThirdScalingUnitClosedBallRGCertificate_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingUnitClosedBallRGCertificate.predictedExponent) :
    halfThirdScalingUnitClosedBallRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_valid_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)
      correlationLength hν


theorem halfThirdScalingUnitClosedBallRGPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
        correlationLength) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      correlationLength :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_valid_of_bridge
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge


theorem halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
        correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_hasCriticalNu_of_bridge
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge


theorem halfThirdScalingUnitClosedBallRGPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      correlationLength :=
  FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_hasCriticalNu
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν


theorem halfThirdScalingUnitClosedBallRGPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      correlationLength :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_valid_of_hasCriticalNu
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν


theorem halfThirdScalingClosedBallCertificate_mapsClosedBall {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailState.MapsClosedBall
      halfThirdScalingCertificate.map zeroState radius := by
  simpa [halfThirdScalingClosedBallCertificate] using
    (halfThirdScalingClosedBallCertificate hradius).mapsClosedBall


theorem halfThirdScalingClosedBallCertificate_fixedPoint_mem {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailState.ClosedBall zeroState radius
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    (halfThirdScalingClosedBallCertificate hradius).fixedPoint_mem


theorem halfThirdScalingClosedBallCertificate_exists_fixedPoint {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ∃ p : FinitePlusTailState 1 ℕ,
      halfThirdScalingCertificate.map p = p ∧
        FinitePlusTailState.ClosedBall zeroState radius p := by
  simpa [halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    (halfThirdScalingClosedBallCertificate hradius).exists_fixedPoint


theorem halfThirdScalingCertificate_iterate_contracts
    (k : ℕ) (x y : FinitePlusTailState 1 ℕ) :
    (halfThirdScalingCertificate.iterate k x).dist
        (halfThirdScalingCertificate.iterate k y) ≤
      ((1 : ℝ) / 2) ^ k * x.dist y := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.iterate_contracts k x y


theorem halfThirdScalingCertificate_iterate_contracts_to_fixedPoint
    (k : ℕ) (x : FinitePlusTailState 1 ℕ) :
    (halfThirdScalingCertificate.iterate k x).dist
        halfThirdScalingCertificate.fixedPoint ≤
      ((1 : ℝ) / 2) ^ k *
        x.dist halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.iterate_dist_le_pow_mul_fixedPoint x k


theorem halfThirdScalingCertificate_iterate_mem_zero_closedBall
    {radius : ℝ} (hradius : 0 ≤ radius)
    {x : FinitePlusTailState 1 ℕ}
    (hx : FinitePlusTailState.ClosedBall zeroState radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall zeroState radius
      (halfThirdScalingCertificate.iterate k x) :=
  halfThirdScalingCertificate.mapsClosedBall_iterate_mem
    (halfThirdScalingCertificate_mapsClosedBall_zero hradius) hx k


theorem halfThirdScalingClosedBallCertificate_iterate_mem
    {radius : ℝ} (hradius : 0 ≤ radius)
    {x : FinitePlusTailState 1 ℕ}
    (hx : FinitePlusTailState.ClosedBall zeroState radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall zeroState radius
      (halfThirdScalingCertificate.iterate k x) := by
  simpa [halfThirdScalingClosedBallCertificate] using
    (halfThirdScalingClosedBallCertificate hradius).iterate_mem hx k


theorem halfThirdScalingClosedBallCertificate_fixedPoint_mem_larger
    {radius radius' : ℝ} (hradius : 0 ≤ radius)
    (hle : radius ≤ radius') :
    FinitePlusTailState.ClosedBall zeroState radius'
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    ((halfThirdScalingClosedBallCertificate hradius).with_larger_radius hle).fixedPoint_mem


theorem halfThirdScalingRadiusOneFromZero_fixedPoint_mem :
    FinitePlusTailState.ClosedBall zeroState 1
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingRadiusOneFromZeroClosedBallCertificate,
    halfThirdScalingRadiusZeroClosedBallCertificate,
    halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    halfThirdScalingRadiusOneFromZeroClosedBallCertificate.fixedPoint_mem


theorem halfThirdScalingUnitClosedBallCertificate_fixedPoint_mem :
    FinitePlusTailState.ClosedBall unitCenterState 1
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingUnitClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    halfThirdScalingUnitClosedBallCertificate.fixedPoint_mem


end FinitePlusTailContractionExample
end Exact3D
end StatMech
