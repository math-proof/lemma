/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part4


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectRawPrimalCrossingTorusComponent_mk
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    SimpleGraph.ConnectedComponent.map
        (SimpleGraph.Hom.ofLE (fkRectOpenGraph_forceCutClosed_le R omega))
        ((fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk x) =
      (fkRectOpenGraph R omega).connectedComponentMk x := by
  exact SimpleGraph.ConnectedComponent.map_mk _ _


end
end StatMech.FrontierD
