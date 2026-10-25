/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalWindingCirculation
    {T : EvenTorus} (row : Fin T.height) (coefficient : Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun v => if v.2 = row then coefficient else 0, fun _ => 0)

end
end StatMech.FrontierD
