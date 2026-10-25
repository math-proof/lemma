/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonCounts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.GenusOneRibbonEulerDefect
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts


namespace StatMech.FrontierD

theorem fkRectTorus_cellularEuler_genus_one (R : FKRectTorus) :
    Fintype.card R.Vertex + fkRectTorusCellularFaceCount R + 2 * 1 =
      Fintype.card R.EdgeIndex + 2 := by
  rw [fkRectTorus_card_vertex, fkRectTorus_card_edgeIndex]
  unfold fkRectTorusCellularFaceCount
  ring


theorem fkRectTorus_vertex_eq_faceCount (R : FKRectTorus) :
    Fintype.card R.Vertex = fkRectTorusCellularFaceCount R := by
  rw [fkRectTorus_card_vertex]
  rfl

end StatMech.FrontierD
