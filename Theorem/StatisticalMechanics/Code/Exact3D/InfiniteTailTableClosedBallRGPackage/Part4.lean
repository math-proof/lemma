/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part4


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


@[simp] theorem with_tableWitness_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tableWitness = W :=
  rfl

@[simp] theorem with_tableWitness_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallRG = P.closedBallRG :=
  rfl

@[simp] theorem with_tableWitness_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tableCertifiedTotalBound =
      W.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_tableWitness_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_tableWitness_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tablePrefixBudget =
      W.tablePrefixBudget :=
  rfl

@[simp] theorem with_tableWitness_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_tableWitness_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tailBudget =
      W.tailBudget :=
  rfl

@[simp] theorem with_tableWitness_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_tableWitness_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallResidual =
      P.closedBallResidual :=
  rfl

@[simp] theorem with_tableWitness_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallRadius =
      P.closedBallRadius :=
  rfl

@[simp] theorem with_tableWitness_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_tableWitness_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_tableWitness_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallFixedPoint =
      P.closedBallFixedPoint :=
  rfl

@[simp] theorem with_tableWitness_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) :
    (P.with_tableWitness W hbudget).certificate scale =
      P.certificate scale :=
  rfl


theorem with_tableWitness_tailTotalTsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    W.tailTotalTsum ≤ P.closedBallResidual := by
  simpa using
    (P.with_tableWitness W hbudget).tailTotalTsum_le_closedBallResidual


theorem with_tableWitness_tail_tsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (∑' a, W.tailContribution a) ≤ P.closedBallResidual := by
  simpa using
    (P.with_tableWitness W hbudget).tail_tsum_le_closedBallResidual


theorem with_tableWitness_tableCertifiedTotalBound_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    W.tableCertifiedTotalBound +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa using
    (P.with_tableWitness W hbudget).tableCertifiedTotalBound_plus_mul_radius_le_radius


theorem with_tableWitness_tailTotalTsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    W.tailTotalTsum +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa using
    (P.with_tableWitness W hbudget).tailTotalTsum_plus_mul_radius_le_radius


theorem with_tableWitness_tail_tsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (∑' a, W.tailContribution a) +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa using
    (P.with_tableWitness W hbudget).tail_tsum_plus_mul_radius_le_radius


theorem with_tableWitness_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) :
    ((P.with_tableWitness W hbudget).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl


theorem with_tableWitness_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_tableWitness W hbudget).certificate scale).RGToExponentBridge
      correlationLength := by
  simpa using hbridge


theorem with_tableWitness_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_tableWitness W hbudget).certificate scale).Valid
      correlationLength := by
  simpa using hvalid


theorem with_tableWitness_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_tableWitness W hbudget).certificate scale).predictedExponent := by
  simpa using hν


end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
