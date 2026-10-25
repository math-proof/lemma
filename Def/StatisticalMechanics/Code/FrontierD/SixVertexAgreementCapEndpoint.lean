/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5


namespace StatMech.FrontierD

noncomputable section

def SixVertexDirectedTorusEdge.IsAgreement
    {T : EvenTorus} (edge : SixVertexDirectedTorusEdge T)
    (omega eta : SixVertexArrows T) : Prop :=
  match edge with
  | .horizontal base _ => omega.horizontal base = eta.horizontal base
  | .vertical base _ => omega.vertical base = eta.vertical base


def SixVertexDirectedSimpleArc.Follows
    {T : EvenTorus} (arc : SixVertexDirectedSimpleArc T)
    (omega : SixVertexArrows T) : Prop :=
  forall i, (arc.edge i).Follows omega


def SixVertexDirectedSimpleArc.IsAgreement
    {T : EvenTorus} (arc : SixVertexDirectedSimpleArc T)
    (omega eta : SixVertexArrows T) : Prop :=
  forall i, (arc.edge i).IsAgreement omega eta


def sixVertexFourByTwoAgreementSuccessor
    (v : sixVertexFourByTwoTorus.Vertex) :
    sixVertexFourByTwoTorus.Vertex :=
  if v.1.val % 2 = v.2.val % 2 then
    (SixVertexArrows.cyclicPred sixVertexFourByTwoTorus.width_pos v.1, v.2)
  else
    (v.1, finitePeriodicSucc sixVertexFourByTwoTorus.height_pos v.2)


end
end StatMech.FrontierD
