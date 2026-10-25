/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part8
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDevelopedSquareCrossingEvent_isIncreasing
    (R : FKRectTorus) (n : Nat) :
    IsIncreasing (fkRectDevelopedSquareCrossingEvent R n) := by
  intro omega tau hot hcross
  rcases hcross with hcross | hcross
  · exact Or.inl
      (fkRectDevelopedSquareHorizontalCrossingEvent_isIncreasing
        R n hot hcross)
  · exact Or.inr
      (fkRectDevelopedSquareVerticalCrossingEvent_isIncreasing
        R n hot hcross)


theorem fkRectDevelopedSquare_dualCompl_subset_crossing
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height) :
    fkRectDualEvent R (fkRectDevelopedSquareCrossingEvent R n)ᶜ ⊆
      fkRectDevelopedSquareCrossingEvent R n := by
  rintro eta ⟨omega, hno, rfl⟩
  have hnoHorizontal :
      omega ∉ fkRectDevelopedSquareHorizontalCrossingEvent R n := by
    intro hcross
    exact hno (Or.inl hcross)
  have hface := fkRectDevelopedSquare_compl_subset_faceDualVertical
    R n hn hnoHorizontal
  exact Or.inr
    (fkRectDevelopedSquare_faceDualVertical_imp_dualVertical
      R n hn hwidth hheight omega hface)


theorem fkRectDevelopedSquareCrossing_ge_one_div_one_add_q
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (1 + q) ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedSquareCrossingEvent R n) := by
  exact one_div_one_add_q_le_eventMass_of_dualCompl_subset R hq _
    (fkRectDevelopedSquare_dualCompl_subset_crossing
      R n hn hwidth hheight)


theorem fkRectDevelopedSquare_exists_direction_crossing_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
        (fkRectDevelopedSquareHorizontalCrossingEvent R n) ∨
      1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
        (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  have hlower := fkRectDevelopedSquareCrossing_ge_one_div_one_add_q
    R n hn hwidth hheight hq
  have hupper := fkRectCriticalEventMass_union_le_add R
    (zero_lt_one.trans_le hq)
    (fkRectDevelopedSquareHorizontalCrossingEvent R n)
    (fkRectDevelopedSquareVerticalCrossingEvent R n)
  have hcross : 1 / (1 + q) ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedSquareHorizontalCrossingEvent R n) +
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
    exact hlower.trans (by
      simpa [fkRectDevelopedSquareCrossingEvent] using hupper)
  have hhalf : 1 / (2 * (1 + q)) = (1 / (1 + q)) / 2 := by
    have hden : 1 + q ≠ 0 := by linarith
    field_simp
  rw [hhalf]
  by_contra h
  push_neg at h
  linarith


end
end StatMech.FrontierD
