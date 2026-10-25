/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5


namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type}


@[simp] theorem with_larger_residual_closedBall
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).closedBall =
      P.closedBall.with_larger_residual hresidual hbudget :=
  rfl

@[simp] theorem with_larger_residual_closedBall_residual
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).closedBall.residual =
      residual' :=
  rfl

@[simp] theorem with_larger_residual_closedBall_fixedPoint
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).closedBall.fixedPoint =
      P.closedBall.fixedPoint :=
  rfl

@[simp] theorem with_larger_residual_thermal
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).thermal = P.thermal :=
  rfl

@[simp] theorem with_larger_residual_certificate_thermalEigenvalue_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_residual hresidual hbudget).certificate
      scale M).thermalEigenvalue = P.thermal :=
  rfl


@[simp] theorem with_larger_residual_certificate_scale_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_residual hresidual hbudget).certificate scale M).scale =
      scale :=
  rfl


@[simp] theorem with_larger_residual_certificate_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.with_larger_residual hresidual hbudget).certificate scale M =
      P.certificate scale M :=
  rfl


theorem with_larger_residual_certificate_predictedExponent_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_residual hresidual hbudget).certificate
      scale M).predictedExponent =
      (P.certificate scale M).predictedExponent :=
  rfl


theorem with_larger_residual_rgToExponentBridge {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    ((P.with_larger_residual hresidual hbudget).certificate scale M).RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_residual_valid {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength) :
    ((P.with_larger_residual hresidual hbudget).certificate scale M).Valid
      correlationLength := by
  simpa using hvalid


theorem with_larger_residual_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_residual hresidual hbudget).certificate
        scale M).predictedExponent := by
  simpa using hν

end FinitePlusTailClosedBallRGPackage
end Exact3D
end StatMech
