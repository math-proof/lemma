/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part2


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


def retarget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) N n where
  tableWitness := P.tableWitness.retarget N
  closedBallRG := P.closedBallRG
  tableBudget_le_residual := by
    simpa [InfiniteTailTableWitnessPackage.retarget,
      InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
      P.tableBudget_le_residual

end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
