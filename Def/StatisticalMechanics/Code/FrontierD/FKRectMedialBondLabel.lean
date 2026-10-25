/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialBondLabel


namespace StatMech.FrontierD

def fkRectMedialBondEdgeIndex (R : FKRectTorus) (e : R.EdgeIndex)
    (side : FKMedialSide) : R.EdgeIndex :=
  match side with
  | .west =>
      if e.1 then (false, e.2)
      else (true, (SixVertexArrows.cyclicPred R.width_pos e.2.1, e.2.2))
  | .east =>
      if e.1 then
        (false, (finitePeriodicSucc R.width_pos e.2.1, e.2.2))
      else (true, e.2)
  | .south =>
      (e.1, (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2))
  | .north =>
      (e.1, (e.2.1, finitePeriodicSucc R.height_pos e.2.2))


end StatMech.FrontierD
