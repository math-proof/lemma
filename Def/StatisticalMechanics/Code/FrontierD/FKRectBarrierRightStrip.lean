/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip


namespace StatMech.FrontierD

noncomputable section

def fkRectSetConnectionWithinEvent (R : FKRectTorus)
    (T X Y : Set R.Vertex) : Set R.Configuration :=
  {omega | ∃ x : T, x.1 ∈ X ∧ ∃ y : T, y.1 ∈ Y ∧
    FKRectConnectedWithin R omega T x y}


end
end StatMech.FrontierD
