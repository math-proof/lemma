/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


noncomputable def tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tableCertifiedTotalBound


noncomputable def tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tableFiniteBudget


noncomputable def tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tablePrefixBudget


noncomputable def tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tailTotalTsum


noncomputable def tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tailBudget


noncomputable def tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    Coord → ℝ :=
  P.tableWitness.tailContribution


def closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.closedBallRG.closedBall.residual


def closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.closedBallRG.closedBall.radius


def closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState n TailIndex :=
  P.closedBallRG.closedBall.center


def closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailLipschitzCertificate n TailIndex :=
  P.closedBallRG.closedBall.contraction


noncomputable def closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState n TailIndex :=
  P.closedBallRG.closedBall.fixedPoint

end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
