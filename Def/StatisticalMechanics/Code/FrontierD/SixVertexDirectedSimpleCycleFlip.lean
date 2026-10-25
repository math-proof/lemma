/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip


namespace StatMech.FrontierD

noncomputable section

def SixVertexDirectedTorusEdge.Follows
    {T : EvenTorus} (edge : SixVertexDirectedTorusEdge T)
    (omega : SixVertexArrows T) : Prop :=
  match edge with
  | .horizontal base positive => omega.horizontal base = positive
  | .vertical base positive => omega.vertical base = positive


def SixVertexDirectedSimpleCycle.Follows
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega : SixVertexArrows T) : Prop :=
  forall i, (cycle.edge i).Follows omega


def SixVertexDirectedSimpleCycle.mask
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T) :
    SixVertexArrows T where
  horizontal base := decide
    (exists i, (cycle.edge i).physical = (false, base))
  vertical base := decide
    (exists i, (cycle.edge i).physical = (true, base))

end
end StatMech.FrontierD
