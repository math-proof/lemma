/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexGeneratedCycleCombination
    (T : EvenTorus)
    (plaquetteWeight : T.Vertex -> Int)
    (horizontalWindingWeight : Fin T.height -> Int)
    (verticalWindingWeight : Fin T.width -> Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun v =>
    (∑ cell : T.Vertex,
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).1 v) +
    (∑ row : Fin T.height,
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).1 v) +
    ∑ column : Fin T.width,
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).1 v,
   fun v =>
    (∑ cell : T.Vertex,
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).2 v) +
    (∑ row : Fin T.height,
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).2 v) +
    ∑ column : Fin T.width,
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).2 v)

end
end StatMech.FrontierD
