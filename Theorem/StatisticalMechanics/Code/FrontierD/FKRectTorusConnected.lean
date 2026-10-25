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
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

theorem fkRect_cyclicPred_eq_sub_one {N : Nat} (hN : 1 < N)
    (i : Fin N) :
    SixVertexArrows.cyclicPred (by omega) i = i - ⟨1, hN⟩ := by
  letI : NeZero N := ⟨by omega⟩
  apply Fin.ext
  simp only [SixVertexArrows.cyclicPred, Fin.val_mk, Fin.sub_def]
  congr 1
  omega

theorem fkRect_cycleGraph_adj_pred_or {N : Nat} (hN : 2 < N)
    {i j : Fin N} (hij : (cycleGraph N).Adj i j) :
    j = SixVertexArrows.cyclicPred (by omega) i ∨
      i = SixVertexArrows.cyclicPred (by omega) j := by
  letI : NeZero N := ⟨by omega⟩
  rw [cycleGraph_adj'] at hij
  let one : Fin N := ⟨1, by omega⟩
  have hone : one.val = 1 := rfl
  rcases hij with hij | hij
  · have hsub : i - j = one := by
      apply Fin.ext
      exact hij.trans hone.symm
    left
    rw [fkRect_cyclicPred_eq_sub_one]
    change j = i - one
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hsub).symm
  · have hsub : j - i = one := by
      apply Fin.ext
      exact hij.trans hone.symm
    right
    rw [fkRect_cyclicPred_eq_sub_one]
    change i = j - one
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hsub).symm


theorem fkRectTorusGraph_adj_verticalPred (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (fkRectTorusGraph R).Adj (x, y)
      (x, SixVertexArrows.cyclicPred R.height_pos y) := by
  exact ⟨(true, (x, y)), rfl⟩


theorem fkRectTorusGraph_reachable_horizontalPred (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (fkRectTorusGraph R).Reachable (x, y)
      (SixVertexArrows.cyclicPred R.width_pos x, y) := by
  let xp := SixVertexArrows.cyclicPred R.width_pos x
  let yp := SixVertexArrows.cyclicPred R.height_pos y
  by_cases hy : Even y.val
  · have hdiag : (fkRectTorusGraph R).Adj (x, y) (xp, yp) := by
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    have hvert : (fkRectTorusGraph R).Adj (xp, y) (xp, yp) :=
      fkRectTorusGraph_adj_verticalPred R xp y
    exact hdiag.reachable.trans hvert.symm.reachable
  · have hvert : (fkRectTorusGraph R).Adj (x, y) (x, yp) :=
      fkRectTorusGraph_adj_verticalPred R x y
    have hdiag : (fkRectTorusGraph R).Adj (xp, y) (x, yp) := by
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    exact hvert.reachable.trans hdiag.symm.reachable


end StatMech.FrontierD
