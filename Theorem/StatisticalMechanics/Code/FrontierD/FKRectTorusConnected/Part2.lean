/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset.Part3
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

theorem fkRectCoordinateCycleGraph_connected (R : FKRectTorus) :
    (fkRectCoordinateCycleGraph R).Connected := by
  let _ : Nonempty (Fin R.width) := Fin.pos_iff_nonempty.mp R.width_pos
  let _ : Nonempty (Fin R.height) := Fin.pos_iff_nonempty.mp R.height_pos
  unfold fkRectCoordinateCycleGraph
  exact ⟨cycleGraph_preconnected.boxProd cycleGraph_preconnected⟩


theorem fkRectTorusGraph_reachable_of_coordinate_adj (R : FKRectTorus)
    {u v : R.Vertex} (huv : (fkRectCoordinateCycleGraph R).Adj u v) :
    (fkRectTorusGraph R).Reachable u v := by
  rcases u with ⟨ux, uy⟩
  rcases v with ⟨vx, vy⟩
  change ((cycleGraph R.width).Adj ux vx ∧ uy = vy) ∨
    ((cycleGraph R.height).Adj uy vy ∧ ux = vx) at huv
  rcases huv with (⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩)
  · subst vy
    rcases fkRect_cycleGraph_adj_pred_or R.width_gt_two hfst with h | h
    · subst vx
      exact fkRectTorusGraph_reachable_horizontalPred R ux uy
    · subst ux
      exact (fkRectTorusGraph_reachable_horizontalPred R vx uy).symm
  · subst vx
    rcases fkRect_cycleGraph_adj_pred_or R.height_gt_two
      (i := uy) (j := vy) hfst with h | h
    · rw [h]
      exact (fkRectTorusGraph_adj_verticalPred R ux uy).reachable
    · rw [h]
      exact (fkRectTorusGraph_adj_verticalPred R ux vy).symm.reachable


theorem fkRectTorusGraph_connected (R : FKRectTorus) :
    (fkRectTorusGraph R).Connected := by
  let _ : Nonempty R.Vertex :=
    ⟨(⟨0, R.width_pos⟩, ⟨0, R.height_pos⟩)⟩
  refine ⟨?_⟩
  intro u v
  have huv := (fkRectCoordinateCycleGraph_connected R).preconnected u v
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv ⊢
  induction huv with
  | refl => rfl
  | tail hxy hyz ih =>
      have hstep := fkRectTorusGraph_reachable_of_coordinate_adj R hyz
      rw [SimpleGraph.reachable_iff_reflTransGen] at hstep
      exact ih.trans hstep

theorem fkRectFinsetClusterCount_univ (R : FKRectTorus) :
    fkRectFinsetClusterCount R Finset.univ = 1 := by
  unfold fkRectFinsetClusterCount fkRectNumClusters
  have hconn :
      (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R Finset.univ)).Connected := by
    rw [fkRectOpenGraph_configurationOfEdges_univ]
    exact fkRectTorusGraph_connected R
  have hcard := card_components_eq_one_of_connected hconn
  simpa only [Nat.card_eq_fintype_card] using hcard

end StatMech.FrontierD
