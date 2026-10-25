/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexPlaquetteBoundaryCirculation
    {T : EvenTorus} (cell : T.Vertex) (coefficient : Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun v => coefficient *
      ((if v = cell then 1 else 0) -
        if v = (cell.1, finitePeriodicSucc T.height_pos cell.2)
        then 1 else 0),
   fun v => coefficient *
      ((if v = (finitePeriodicSucc T.width_pos cell.1, cell.2)
        then 1 else 0) - if v = cell then 1 else 0))

end
end StatMech.FrontierD
