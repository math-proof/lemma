/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleCount
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel


namespace StatMech.FrontierD

def fkRectMedialWestPrimal (R : FKRectTorus) (e : R.EdgeIndex) : R.Vertex :=
  if e.1 then
    if Even e.2.2.val then e.2
    else (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2)
  else if Even e.2.2.val then
    (SixVertexArrows.cyclicPred R.width_pos e.2.1,
      SixVertexArrows.cyclicPred R.height_pos e.2.2)
  else
    (SixVertexArrows.cyclicPred R.width_pos e.2.1, e.2.2)


def fkRectMedialEastPrimal (R : FKRectTorus) (e : R.EdgeIndex) : R.Vertex :=
  if e.1 then
    if Even e.2.2.val then
      (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2)
    else e.2
  else if Even e.2.2.val then e.2
  else (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2)


end StatMech.FrontierD
