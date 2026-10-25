/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectVerticalEndpointPairs (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) :
    Finset ((fkRectVertexRectangle R x0 x1 y0 y1) ×
      (fkRectVertexRectangle R x0 x1 y0 y1)) :=
  Finset.univ.filter fun p =>
    p.1.1.2.val = y0 ∧ p.2.1.2.val = y1


def fkRectVerticalEndpointConnectionEvent (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat)
    (p : (fkRectVertexRectangle R x0 x1 y0 y1) ×
      (fkRectVertexRectangle R x0 x1 y0 y1)) : Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectVertexRectangle R x0 x1 y0 y1) p.1 p.2}

end
end StatMech.FrontierD
