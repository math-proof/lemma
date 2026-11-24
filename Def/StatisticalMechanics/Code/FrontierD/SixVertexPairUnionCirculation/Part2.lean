module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexPairUnionHorizontalDelta
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  sixVertexPairUnionHorizontal target v -
    sixVertexPairUnionHorizontal source v


def sixVertexPairUnionVerticalDelta
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  sixVertexPairUnionVertical target v -
    sixVertexPairUnionVertical source v


end
end StatMech.FrontierD
