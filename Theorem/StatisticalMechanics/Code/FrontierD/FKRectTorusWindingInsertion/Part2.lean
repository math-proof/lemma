/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectLocalCriterion
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingInsertion
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectInsertedFundamentalWalk_winding
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e p) =
      ((fkRectWalkWinding R p).1 +
          fkRectHorizontalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e),
        (fkRectWalkWinding R p).2 +
          fkRectVerticalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e)) := by
  unfold fkRectInsertedFundamentalWalk
  rw [SimpleGraph.Walk.concat_eq_append, fkRectWalkWinding_append,
    fkRectWalkWinding_mapLe]
  simp [fkRectWalkWinding]


theorem FKRectHasNet_insert_of_independent_fundamentalWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (q : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e))
    (hind : FKRectWindingIndependent (fkRectWalkWinding R q)
      ((fkRectWalkWinding R p).1 +
          fkRectHorizontalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e),
        (fkRectWalkWinding R p).2 +
          fkRectVerticalSeamIncrement R
            (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e))) :
    FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) := by
  let hgraph := fkRectOpenGraph_le_insert R F e
  refine ⟨fkRectMedialWestPrimal R e, q.mapLe hgraph,
    fkRectInsertedFundamentalWalk R F e p, ?_⟩
  rw [fkRectWalkWinding_mapLe,
    fkRectInsertedFundamentalWalk_winding]
  exact hind

end
end StatMech.FrontierD
