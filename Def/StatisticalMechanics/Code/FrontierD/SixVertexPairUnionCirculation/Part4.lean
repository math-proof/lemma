/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexVerticalWindingCirculation
    {T : EvenTorus} (column : Fin T.width) (coefficient : Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun _ => 0, fun v => if v.1 = column then coefficient else 0)

end
end StatMech.FrontierD
