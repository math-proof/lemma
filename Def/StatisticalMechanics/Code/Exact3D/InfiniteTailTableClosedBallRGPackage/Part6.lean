/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part5


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


noncomputable def with_tableWitness_as_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n :=
  (P.with_larger_closedBallResidual
    (residual' := W.tableCertifiedTotalBound)
    (by simpa [closedBallResidual] using hresidual)
    (by simpa [closedBallContraction, closedBallRadius] using hbudget)
  ).with_tableWitness W (by rfl)

end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
