/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part2


namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type}


@[simp] theorem certificate_thermalEigenvalue_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).thermalEigenvalue = thermal :=
  rfl


@[simp] theorem certificate_scale_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).scale = scale :=
  rfl

@[simp] theorem certificate_fixedPoint_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).fixedPointData.fixedPoint =
      C.fixedPoint :=
  rfl

@[simp] theorem certificate_R_map_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).R.map = C.contraction.map :=
  rfl


theorem certificate_predictedExponent_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).predictedExponent =
      predictedNu scale thermal :=
  rfl


theorem certificate_fixedPointEnclosure {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).FixedPointEnclosure :=
  C.fixedPoint_isFixed


theorem certificate_finiteCaseChecks {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).FiniteCaseChecks :=
  trivial


theorem certificate_tailBounds {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).TailBounds :=
  trivial


theorem certificate_linearizationEnclosure {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).LinearizationEnclosure :=
  (C.certificate scale M thermal hthermal).linearizationEnclosure_of_thermal_gt_one


theorem certificate_hyperbolicSplitting {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).HyperbolicSplitting :=
  (C.certificate scale M thermal hthermal).hyperbolicSplitting_of_thermal_gt_one


theorem certificate_orbitEntry {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).OrbitEntry :=
  trivial


theorem certificate_fixedPoint_mem_closedBall {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    FinitePlusTailState.ClosedBall C.center C.radius
      (C.certificate scale M thermal hthermal).fixedPointData.fixedPoint := by
  simpa [certificate, fixedPointData] using C.fixedPoint_mem


theorem rgMap_iterate_eq
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (k : ℕ) (x : FinitePlusTailState n α) :
    ((C.rgMap scale).map^[k]) x = C.contraction.iterate k x := by
  induction k with
  | zero =>
      simp [FinitePlusTailLipschitzCertificate.iterate]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simpa [rgMap, FinitePlusTailLipschitzCertificate.iterate] using
        congrArg C.contraction.map ih


theorem rgMap_iterate_mem_closedBall
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale)
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall C.center C.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center C.radius
      (((C.rgMap scale).map^[k]) x) := by
  rw [C.rgMap_iterate_eq scale k x]
  exact C.iterate_mem hx k


theorem certificate_iterate_mem_closedBall {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {x : (C.certificate scale M thermal hthermal).H.carrier}
    (hx : FinitePlusTailState.ClosedBall C.center C.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center C.radius
      ((((C.certificate scale M thermal hthermal).R.map)^[k]) x) := by
  simpa [certificate] using C.rgMap_iterate_mem_closedBall scale hx k


theorem certificate_valid_of_bridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    (C.certificate scale M thermal hthermal).Valid correlationLength where
  finiteCaseChecks :=
    C.certificate_finiteCaseChecks scale M thermal hthermal
  tailBounds := C.certificate_tailBounds scale M thermal hthermal
  fixedPointEnclosure :=
    C.certificate_fixedPointEnclosure scale M thermal hthermal
  linearizationEnclosure :=
    C.certificate_linearizationEnclosure scale M thermal hthermal
  hyperbolicSplitting :=
    C.certificate_hyperbolicSplitting scale M thermal hthermal
  orbitEntry := C.certificate_orbitEntry scale M thermal hthermal
  bridge := hbridge


theorem certificate_rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    (C.certificate scale M thermal hthermal).RGToExponentBridge
      correlationLength := by
  simpa [RGCertificate.RGToExponentBridge] using hν


theorem certificate_valid_of_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    (C.certificate scale M thermal hthermal).Valid correlationLength :=
  C.certificate_valid_of_bridge
    scale M thermal hthermal correlationLength
    (C.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M thermal hthermal correlationLength hν)


theorem certificate_hasCriticalNu_of_bridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    HasCriticalNu M correlationLength
      (C.certificate scale M thermal hthermal).predictedExponent :=
  (C.certificate_valid_of_bridge
    scale M thermal hthermal correlationLength hbridge).hasCriticalNu


@[simp] theorem with_larger_radius_certificate_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.with_larger_radius hradius).certificate scale M thermal hthermal =
      C.certificate scale M thermal hthermal :=
  rfl


theorem with_larger_radius_rgToExponentBridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    ((C.with_larger_radius hradius).certificate scale M thermal hthermal).RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_radius_valid {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (C.certificate scale M thermal hthermal).Valid correlationLength) :
    ((C.with_larger_radius hradius).certificate scale M thermal hthermal).Valid
      correlationLength := by
  simpa using hvalid


theorem with_larger_radius_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    HasCriticalNu M correlationLength
      ((C.with_larger_radius hradius).certificate
        scale M thermal hthermal).predictedExponent := by
  simpa using hν


@[simp] theorem with_larger_residual_certificate_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.with_larger_residual hresidual hbudget).certificate
      scale M thermal hthermal =
      C.certificate scale M thermal hthermal :=
  rfl


theorem with_larger_residual_rgToExponentBridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    ((C.with_larger_residual hresidual hbudget).certificate
      scale M thermal hthermal).RGToExponentBridge correlationLength := by
  simpa using hbridge


theorem with_larger_residual_valid {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (C.certificate scale M thermal hthermal).Valid correlationLength) :
    ((C.with_larger_residual hresidual hbudget).certificate
      scale M thermal hthermal).Valid correlationLength := by
  simpa using hvalid


theorem with_larger_residual_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    HasCriticalNu M correlationLength
      ((C.with_larger_residual hresidual hbudget).certificate
        scale M thermal hthermal).predictedExponent := by
  simpa using hν

end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
