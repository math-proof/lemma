/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial


namespace StatMech.FrontierD

def fkRectTorusIndexedEdge (R : FKRectTorus) (a : R.EdgeIndex) :
    Sym2 R.Vertex :=
  if a.1 then
    s(a.2, (a.2.1, SixVertexArrows.cyclicPred R.height_pos a.2.2))
  else if Even a.2.2.val then
    s(a.2, (SixVertexArrows.cyclicPred R.width_pos a.2.1,
      SixVertexArrows.cyclicPred R.height_pos a.2.2))
  else
    s((SixVertexArrows.cyclicPred R.width_pos a.2.1, a.2.2),
      (a.2.1, SixVertexArrows.cyclicPred R.height_pos a.2.2))

end StatMech.FrontierD
