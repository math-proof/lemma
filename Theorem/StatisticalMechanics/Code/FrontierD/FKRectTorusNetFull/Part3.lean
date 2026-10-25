/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectWalkWinding_concat (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {u v w : R.Vertex}
    (p : G.Walk u v) (h : G.Adj v w) :
    fkRectWalkWinding R (p.concat h) =
      ((fkRectWalkWinding R p).1 + fkRectHorizontalSeamIncrement R v w,
        (fkRectWalkWinding R p).2 + fkRectVerticalSeamIncrement R v w) := by
  rw [SimpleGraph.Walk.concat_eq_append, fkRectWalkWinding_append]
  simp [fkRectWalkWinding]

theorem fkRectVerticalFundamentalWalkAux_winding (R : FKRectTorus)
    (x : Fin R.width) (n : Nat) (hn : n <= R.height) :
    fkRectWalkWinding R
      (fkRectVerticalFundamentalWalkAux R x
        (⟨0, R.height_pos⟩ : Fin R.height) n) =
      (0, if n = 0 then 0 else -1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n <= R.height := by omega
      rw [fkRectVerticalFundamentalWalkAux, fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      rw [fkRectHorizontalSeamIncrement_same_fst, fkRectVerticalSeamIncrement_pred]
      have hval := fkRectCyclicPred_iterate_zero_val R.height_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.height := by omega
        simp [hzero]
        omega

theorem fkRectHorizontalFundamentalWalkAux_winding (R : FKRectTorus)
    (n : Nat) (hn : n <= R.width) :
    fkRectWalkWinding R
      (fkRectHorizontalFundamentalWalkAux R
        (⟨0, R.width_pos⟩ : Fin R.width) n) =
      (if n = 0 then 0 else -1, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n <= R.width := by omega
      rw [fkRectHorizontalFundamentalWalkAux, fkRectWalkWinding_concat,
        fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      rw [fkRectHorizontalSeamIncrement_same_fst,
        fkRectVerticalSeamIncrement_pred_zero_reverse,
        fkRectHorizontalSeamIncrement_pred,
        fkRectVerticalSeamIncrement_pred_zero]
      have hval := fkRectCyclicPred_iterate_zero_val R.width_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.width := by omega
        simp [hzero]
        omega

theorem fkRectCyclicPred_iterate_zero_card {N : Nat} (hN : 0 < N) :
    (SixVertexArrows.cyclicPred hN)^[N] (⟨0, hN⟩ : Fin N) =
      (⟨0, hN⟩ : Fin N) := by
  apply Fin.ext
  rw [fkRectCyclicPred_iterate_zero_val hN N (le_refl N)]
  simp

end
end StatMech.FrontierD
