/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part4


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


def with_larger_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n where
  tableWitness := P.tableWitness
  closedBallRG :=
    P.closedBallRG.with_larger_residual hresidual hbudget
  tableBudget_le_residual := le_trans P.tableBudget_le_residual hresidual


def with_larger_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n where
  tableWitness := P.tableWitness
  closedBallRG := P.closedBallRG.with_larger_radius hradius
  tableBudget_le_residual := P.tableBudget_le_residual

end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
