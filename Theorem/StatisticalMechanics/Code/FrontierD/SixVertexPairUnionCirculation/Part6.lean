/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexGeneratedCycleCombination_isCirculation
    (T : EvenTorus)
    (plaquetteWeight : T.Vertex -> Int)
    (horizontalWindingWeight : Fin T.height -> Int)
    (verticalWindingWeight : Fin T.width -> Int) :
    SixVertexTorusCirculation T
      (sixVertexGeneratedCycleCombination T plaquetteWeight
        horizontalWindingWeight verticalWindingWeight).1
      (sixVertexGeneratedCycleCombination T plaquetteWeight
        horizontalWindingWeight verticalWindingWeight).2 := by
  let plaquettes := sixVertexTorusCirculation_sum
    (fun cell : T.Vertex =>
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).1)
    (fun cell : T.Vertex =>
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).2)
    (fun cell =>
      sixVertexPlaquetteBoundaryCirculation_isCirculation
        cell (plaquetteWeight cell))
  let horizontalWindings := sixVertexTorusCirculation_sum
    (fun row : Fin T.height =>
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).1)
    (fun row : Fin T.height =>
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).2)
    (fun row =>
      sixVertexHorizontalWindingCirculation_isCirculation
        row (horizontalWindingWeight row))
  let verticalWindings := sixVertexTorusCirculation_sum
    (fun column : Fin T.width =>
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).1)
    (fun column : Fin T.width =>
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).2)
    (fun column =>
      sixVertexVerticalWindingCirculation_isCirculation
        column (verticalWindingWeight column))
  exact (plaquettes.add horizontalWindings).add verticalWindings

end
end StatMech.FrontierD
