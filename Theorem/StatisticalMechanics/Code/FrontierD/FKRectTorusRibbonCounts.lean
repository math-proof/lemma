/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonCounts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.GenusOneRibbonEulerDefect
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5


namespace StatMech.FrontierD

theorem fkRectTorus_card_vertex (R : FKRectTorus) :
    Fintype.card R.Vertex = R.width * R.height := by
  simp [FKRectTorus.Vertex]


theorem fkRectTorus_card_edgeIndex (R : FKRectTorus) :
    Fintype.card R.EdgeIndex = 2 * R.width * R.height := by
  simp [FKRectTorus.EdgeIndex]
  ring


end StatMech.FrontierD
