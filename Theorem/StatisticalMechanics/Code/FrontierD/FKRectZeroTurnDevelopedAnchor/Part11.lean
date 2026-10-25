/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part10
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (hincidence : FKRectZeroTurnPrimalDevelopedExtremeIncidence R omega)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D)
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) : C = D := by
  apply Subtype.ext
  rw [← hincidence C X hXC, ← hincidence D X hXD, hside]

end
end StatMech.FrontierD
