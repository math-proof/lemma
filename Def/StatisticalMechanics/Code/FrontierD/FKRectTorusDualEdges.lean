/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9


namespace StatMech.FrontierD

noncomputable section

def fkRectEdgeToDualEdge (R : FKRectTorus) (e : R.EdgeIndex) : R.EdgeIndex :=
  if e.1 then
    (false, e.2)
  else
    (true, (SixVertexArrows.cyclicPred R.width_pos e.2.1, e.2.2))


def fkRectDualEdgeToEdge (R : FKRectTorus) (e : R.EdgeIndex) : R.EdgeIndex :=
  if e.1 then
    (false, (finitePeriodicSucc R.width_pos e.2.1, e.2.2))
  else
    (true, e.2)

end
end StatMech.FrontierD
