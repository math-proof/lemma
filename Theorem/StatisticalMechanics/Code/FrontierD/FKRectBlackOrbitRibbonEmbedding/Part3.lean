/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part3


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectMedialRibbonBlockOffset_eq_table
    (pairing : Bool) (side : FKMedialSide) :
    fkRectMedialRibbonBlockOffset pairing side =
      fkRectMedialRibbonBlockOffsetTable pairing side := by
  funext t
  cases pairing <;> cases side <;> fin_cases t <;>
    decide


end
end StatMech.FrontierD
