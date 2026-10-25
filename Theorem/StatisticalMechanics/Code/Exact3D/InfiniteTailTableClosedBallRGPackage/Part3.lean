/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part3


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


@[simp] theorem retarget_tableWitness {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tableWitness = P.tableWitness.retarget N :=
  rfl

@[simp] theorem retarget_tailContribution {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tailContribution = P.tailContribution :=
  rfl

@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tailTotalTsum = P.tailTotalTsum :=
  rfl

@[simp] theorem retarget_closedBallRG {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallRG = P.closedBallRG :=
  rfl

@[simp] theorem retarget_tableCertifiedTotalBound {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tableCertifiedTotalBound = P.tableCertifiedTotalBound :=
  rfl

@[simp] theorem retarget_tableFiniteBudget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tableFiniteBudget = P.tableFiniteBudget :=
  rfl

@[simp] theorem retarget_tablePrefixBudget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tablePrefixBudget = P.tablePrefixBudget :=
  rfl

@[simp] theorem retarget_tailBudget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tailBudget = P.tailBudget :=
  rfl

@[simp] theorem retarget_closedBallResidual {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallResidual = P.closedBallResidual :=
  rfl

@[simp] theorem retarget_closedBallRadius {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallRadius = P.closedBallRadius :=
  rfl

@[simp] theorem retarget_closedBallCenter {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallCenter = P.closedBallCenter :=
  rfl

@[simp] theorem retarget_closedBallContraction {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallContraction = P.closedBallContraction :=
  rfl

@[simp] theorem retarget_closedBallFixedPoint {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallFixedPoint = P.closedBallFixedPoint :=
  rfl

@[simp] theorem retarget_certificate {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale) :
    (P.retarget N).certificate scale = (P.certificate scale).retarget N :=
  rfl

@[simp] theorem retarget_predictedExponent {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale) :
    ((P.retarget N).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl


theorem retarget_rgToExponentBridge {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    ((P.retarget N).certificate scale).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc


theorem retarget_valid {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    ((P.retarget N).certificate scale).Valid correlationLength := by
  simpa using hvalid.retarget hβc


theorem retarget_hasCriticalNu {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      ((P.retarget N).certificate scale).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc


theorem retarget_rgToExponentBridge_iff {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale).RGToExponentBridge correlationLength ↔
      ((P.retarget N).certificate scale).RGToExponentBridge
        correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := P.certificate scale) (N := N) hβc)


theorem retarget_valid_iff {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale).Valid correlationLength ↔
      ((P.retarget N).certificate scale).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := P.certificate scale) (N := N) hβc)


theorem retarget_hasCriticalNu_iff {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent ↔
      HasCriticalNu N correlationLength
        ((P.retarget N).certificate scale).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := P.certificate scale) (N := N) hβc)


end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
