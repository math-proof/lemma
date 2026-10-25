/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation


namespace StatMech.FrontierD

noncomputable section

def SixVertexDirectedSimpleCycle.horizontalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (v : T.Vertex) : Int :=
  ∑ i, (cycle.edge i).horizontalFlow v

def SixVertexDirectedSimpleCycle.verticalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (v : T.Vertex) : Int :=
  ∑ i, (cycle.edge i).verticalFlow v


end
end StatMech.FrontierD
