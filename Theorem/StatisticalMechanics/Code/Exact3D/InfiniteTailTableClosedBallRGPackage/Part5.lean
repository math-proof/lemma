/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part5


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


@[simp] theorem with_larger_closedBallRadius_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tableWitness =
      P.tableWitness :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallRG =
      P.closedBallRG.with_larger_radius hradius :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallRadius =
      radius' :=
  by
    simp [with_larger_closedBallRadius, closedBallRadius,
      FinitePlusTailClosedBallRGPackage.with_larger_radius]

@[simp] theorem with_larger_closedBallRadius_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallResidual =
      P.closedBallResidual :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simp [closedBallFixedPoint, with_larger_closedBallRadius]

@[simp] theorem with_larger_closedBallRadius_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tableCertifiedTotalBound =
      P.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tableFiniteBudget =
      P.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tablePrefixBudget =
      P.tablePrefixBudget :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tailTotalTsum =
      P.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tailBudget =
      P.tailBudget :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tailContribution =
      P.tailContribution :=
  rfl

@[simp] theorem with_larger_closedBallRadius_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) :
    (P.with_larger_closedBallRadius hradius).certificate scale =
      P.certificate scale :=
  rfl


theorem with_larger_closedBallRadius_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) :
    ((P.with_larger_closedBallRadius hradius).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl


theorem with_larger_closedBallRadius_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_larger_closedBallRadius hradius).certificate scale).RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_larger_closedBallRadius_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_larger_closedBallRadius hradius).certificate scale).Valid
      correlationLength := by
  simpa using hvalid


theorem with_larger_closedBallRadius_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_closedBallRadius hradius).certificate
        scale).predictedExponent := by
  simpa using hν

@[simp] theorem with_larger_closedBallResidual_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tableWitness =
      P.tableWitness :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallRG =
      P.closedBallRG.with_larger_residual hresidual hbudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallResidual =
      residual' :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallRadius =
      P.closedBallRadius :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simp [closedBallFixedPoint, with_larger_closedBallResidual]

@[simp] theorem with_larger_closedBallResidual_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual
      hresidual hbudget).tableCertifiedTotalBound =
      P.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tableFiniteBudget =
      P.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tablePrefixBudget =
      P.tablePrefixBudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tailTotalTsum =
      P.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tailBudget =
      P.tailBudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tailContribution =
      P.tailContribution :=
  rfl

@[simp] theorem with_larger_closedBallResidual_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) :
    (P.with_larger_closedBallResidual hresidual hbudget).certificate scale =
      P.certificate scale :=
  rfl


theorem with_larger_closedBallResidual_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) :
    ((P.with_larger_closedBallResidual
      hresidual hbudget).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl


theorem with_larger_closedBallResidual_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_larger_closedBallResidual hresidual hbudget).certificate
      scale).RGToExponentBridge correlationLength := by
  simpa using hbridge


theorem with_larger_closedBallResidual_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_larger_closedBallResidual hresidual hbudget).certificate
      scale).Valid correlationLength := by
  simpa using hvalid


theorem with_larger_closedBallResidual_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_closedBallResidual hresidual hbudget).certificate
        scale).predictedExponent := by
  simpa using hν


end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
