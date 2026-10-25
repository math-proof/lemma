/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part3


namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type}


@[simp] theorem certificate_retarget {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ) :
    P.certificate scale N = (P.certificate scale M).retarget N :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).thermalEigenvalue = P.thermal :=
  rfl


@[simp] theorem certificate_scale_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).scale = scale :=
  rfl


@[simp] theorem certificate_fixedPoint_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).fixedPointData.fixedPoint =
      P.closedBall.fixedPoint :=
  rfl


@[simp] theorem certificate_R_map_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).R.map = P.closedBall.contraction.map :=
  rfl


theorem certificate_predictedExponent_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).predictedExponent =
      predictedNu scale P.thermal :=
  rfl


theorem mapsClosedBall
    (P : FinitePlusTailClosedBallRGPackage n α) :
    FinitePlusTailState.MapsClosedBall
      P.closedBall.contraction.map P.closedBall.center P.closedBall.radius :=
  P.closedBall.mapsClosedBall


theorem fixedPoint_mem_closedBall
    (P : FinitePlusTailClosedBallRGPackage n α) :
    FinitePlusTailState.ClosedBall
      P.closedBall.center P.closedBall.radius P.closedBall.fixedPoint :=
  P.closedBall.fixedPoint_mem


theorem certificate_fixedPointEnclosure {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).FixedPointEnclosure := by
  simpa [certificate] using
    P.closedBall.certificate_fixedPointEnclosure
      scale M P.thermal P.thermal_gt_one


theorem certificate_finiteCaseChecks {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).FiniteCaseChecks := by
  simpa [certificate] using
    P.closedBall.certificate_finiteCaseChecks
      scale M P.thermal P.thermal_gt_one


theorem certificate_tailBounds {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).TailBounds := by
  simpa [certificate] using
    P.closedBall.certificate_tailBounds
      scale M P.thermal P.thermal_gt_one


theorem certificate_linearizationEnclosure {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).LinearizationEnclosure := by
  simpa [certificate] using
    P.closedBall.certificate_linearizationEnclosure
      scale M P.thermal P.thermal_gt_one


theorem certificate_hyperbolicSplitting {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).HyperbolicSplitting := by
  simpa [certificate] using
    P.closedBall.certificate_hyperbolicSplitting
      scale M P.thermal P.thermal_gt_one


theorem certificate_orbitEntry {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).OrbitEntry := by
  simpa [certificate] using
    P.closedBall.certificate_orbitEntry
      scale M P.thermal P.thermal_gt_one


theorem certificate_fixedPoint_mem_closedBall {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    FinitePlusTailState.ClosedBall
      P.closedBall.center P.closedBall.radius
      (P.certificate scale M).fixedPointData.fixedPoint := by
  simpa [certificate] using
    P.closedBall.certificate_fixedPoint_mem_closedBall
      scale M P.thermal P.thermal_gt_one


theorem certificate_iterate_mem_closedBall {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {x : (P.certificate scale M).H.carrier}
    (hx :
      FinitePlusTailState.ClosedBall
        P.closedBall.center P.closedBall.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall
      P.closedBall.center P.closedBall.radius
      ((((P.certificate scale M).R.map)^[k]) x) := by
  simpa [certificate] using
    P.closedBall.certificate_iterate_mem_closedBall
      scale M P.thermal P.thermal_gt_one hx k


theorem certificate_valid_of_bridge {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    (P.certificate scale M).Valid correlationLength := by
  simpa [certificate] using
    P.closedBall.certificate_valid_of_bridge
      scale M P.thermal P.thermal_gt_one correlationLength hbridge


theorem certificate_rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    (P.certificate scale M).RGToExponentBridge correlationLength := by
  simpa [certificate] using
    P.closedBall.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M P.thermal P.thermal_gt_one correlationLength hν


theorem certificate_valid_of_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M correlationLength hν)


theorem certificate_hasCriticalNu_of_bridge {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_bridge
    scale M correlationLength hbridge).hasCriticalNu


theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred


theorem certificate_valid_of_bridge_congr_predictedExponent {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
      scale M hpred hbridge)


theorem certificate_hasCriticalNu_of_bridge_congr_predictedExponent
    {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_bridge_congr_predictedExponent
    scale M hpred hbridge).hasCriticalNu


theorem certificate_retarget_rgToExponentBridge {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc


theorem certificate_retarget_valid {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale N).Valid correlationLength := by
  simpa using hvalid.retarget hβc


theorem certificate_retarget_hasCriticalNu {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      (P.certificate scale N).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc


theorem certificate_retarget_rgToExponentBridge_iff {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale M).RGToExponentBridge correlationLength ↔
      (P.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := P.certificate scale M) (N := N) hβc)


theorem certificate_retarget_valid_iff {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale M).Valid correlationLength ↔
      (P.certificate scale N).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := P.certificate scale M) (N := N) hβc)


theorem certificate_retarget_hasCriticalNu_iff {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent ↔
      HasCriticalNu N correlationLength
        (P.certificate scale N).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := P.certificate scale M) (N := N) hβc)


end FinitePlusTailClosedBallRGPackage
end Exact3D
end StatMech
