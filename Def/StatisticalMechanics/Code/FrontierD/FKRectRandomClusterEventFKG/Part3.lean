/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectTorusConnectionChainEvent (R : FKRectTorus)
    (s : Finset (R.Vertex × R.Vertex)) : Set R.Configuration :=
  fkRectFiniteEventIntersection s fun p =>
    fkRectTorusConnectionEvent R p.1 p.2

end
end StatMech.FrontierD
