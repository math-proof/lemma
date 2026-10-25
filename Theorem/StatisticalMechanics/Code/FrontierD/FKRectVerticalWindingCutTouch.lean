/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberBalance
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_touch
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectHorizontalCutEdges R) :
    fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val = 0 at ha
  have hlast : R.height - 1 + 1 = R.height := by omega
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk]
    all_goals rw [fkRectCyclicPred_val]
    all_goals simp only [ha, if_true]
    all_goals exact Or.inl ⟨True.intro, hlast⟩
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk]
    rw [fkRectCyclicPred_val]
    simp only [ha, if_true]
    exact Or.inl ⟨True.intro, hlast⟩


theorem fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Adj x y)
    (hnot : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).Adj x y := by
  rcases hxy with ⟨a, hopen, hedge⟩
  refine ⟨a, ?_, hedge⟩
  have hcut : a ∉ fkRectHorizontalCutEdges R := by
    intro ha
    apply hnot
    rw [← hedge]
    exact fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_touch
      R a ha
  simpa [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed, hcut]
    using hopen


end
end StatMech.FrontierD
