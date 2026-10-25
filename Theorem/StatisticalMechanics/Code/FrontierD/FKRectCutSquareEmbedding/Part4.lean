/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part3
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVertexBoxEmbedding_injective (R : FKRectTorus) :
    Function.Injective (fkRectVertexBoxEmbedding R) := by
  intro x y hxy
  apply fkRectVertexSquareSite_injective R
  exact congrArg Subtype.val hxy


theorem fkRectCutGraph_boxAdjMatch (R : FKRectTorus) :
    FK.ocd_AdjMatch (fkRectCutGraph R)
      (FK.boxGraph 2 (R.width + R.height))
      (fkRectVertexBoxEmbedding R) := by
  intro x y
  rw [fkRectCutGraph_adj_iff_hypercubicAdj]
  rfl


end
end StatMech.FrontierD
