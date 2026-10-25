/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part6


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


@[simp] theorem with_tableWitness_as_closedBallResidual_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tableWitness =
      W :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallRG =
      P.closedBallRG.with_larger_residual
        (by simpa [closedBallResidual] using hresidual)
        (by simpa [closedBallContraction, closedBallRadius] using hbudget) :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallResidual =
      W.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallRadius =
      P.closedBallRadius :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simp [with_tableWitness_as_closedBallResidual]

@[simp] theorem with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tableCertifiedTotalBound =
      W.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tablePrefixBudget =
      W.tablePrefixBudget :=
  rfl


theorem
    with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound_eq_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tableCertifiedTotalBound =
      (P.with_tableWitness_as_closedBallResidual
        W hresidual hbudget).closedBallResidual := by
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound,
    with_tableWitness_as_closedBallResidual_closedBallResidual]

@[simp] theorem with_tableWitness_as_closedBallResidual_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tailBudget =
      W.tailBudget :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale =
      P.certificate scale :=
  rfl


theorem
    with_tableWitness_as_closedBallResidual_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) :
    ((P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl


theorem with_tableWitness_as_closedBallResidual_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale).RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_tableWitness_as_closedBallResidual_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale).Valid correlationLength := by
  simpa using hvalid


theorem with_tableWitness_as_closedBallResidual_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_tableWitness_as_closedBallResidual
        W hresidual hbudget).certificate scale).predictedExponent := by
  simpa using hν

end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
