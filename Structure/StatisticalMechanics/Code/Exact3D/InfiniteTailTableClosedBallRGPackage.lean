/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5


namespace StatMech

namespace Exact3D

structure InfiniteTailTableClosedBallRGPackage
    {ι Case Coord : Type*} {TailIndex : Type}
    [DecidableEq Case] [DecidableEq Coord]
    (M : CriticalModel ι) (n : ℕ) where
  tableWitness :
    InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M
  closedBallRG : FinitePlusTailClosedBallRGPackage n TailIndex
  tableBudget_le_residual :
    tableWitness.tableCertifiedTotalBound ≤ closedBallRG.closedBall.residual

end Exact3D
end StatMech
