/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexPairUnionHorizontal
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  (pair.1.horizontal v).toNat + (pair.2.horizontal v).toNat


def sixVertexPairUnionVertical
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  (pair.1.vertical v).toNat + (pair.2.vertical v).toNat


def SixVertexTorusCirculation
    (T : EvenTorus) (horizontal vertical : T.Vertex -> Int) : Prop :=
  forall v,
    horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
        vertical (v.1,
          SixVertexArrows.cyclicPred T.height_pos v.2) =
      horizontal v + vertical v


end
end StatMech.FrontierD
