/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectLeftStrip (R : FKRectTorus) (right : Nat) : Set R.Vertex :=
  {v | v.1.val ≤ right}

def fkRectColumnSet (R : FKRectTorus) (column : Nat) : Set R.Vertex :=
  {v | v.1.val = column}


def fkRectNoLeftStripCrossingEvent (R : FKRectTorus)
    (right : Nat) : Set R.Configuration :=
  (fkRectSetConnectionWithinEvent R
    (fkRectLeftStrip R right)
    (fkRectColumnSet R 0)
    (fkRectColumnSet R right))ᶜ

end
end StatMech.FrontierD
