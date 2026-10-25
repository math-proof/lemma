/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part3


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCSHeadingFits_start :
    HexCSHeadingFits hexCSOutsideStartCoord (hexCSHeadingFin 1) := by
  simp [HexCSHeadingFits, hexCSOutsideStartCoord]

theorem hexCSEdgeOfHeading_mod (c : HexAWCoord) (h : Fin 6)
    (hfit : HexCSHeadingFits c h) :
    hexAWHeadingMod c (hexCSEdgeOfHeading c h) = h := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases h <;>
    simp [HexCSHeadingFits, hexCSEdgeOfHeading,
      hexAWHeadingMod] at hfit ⊢

theorem hexAWHeadingMod_unit (c : HexAWCoord) (e : Fin 3) :
    hexUnit (hexAWHeading c e) =
      hexUnit (hexAWHeadingMod c e).val := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexAWHeading, hexAWHeadingMod]
  rw [show (7 : ℤ) = 1 + 6 by norm_num, hexUnit_add_six]

theorem hexCSEdgeOfHeading_halfStep
    (c : HexAWCoord) (h0 : ℤ)
    (hfit : HexCSHeadingFits c (hexCSHeadingFin h0)) :
    halfStep h0 =
    halfStep (hexAWHeading c
        (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) := by
  have hu := hexCSHeadingFin_unit h0
  have hm := hexCSEdgeOfHeading_mod c (hexCSHeadingFin h0) hfit
  have he := hexAWHeadingMod_unit c
    (hexCSEdgeOfHeading c (hexCSHeadingFin h0))
  calc
    halfStep h0 = (1 / 2 : ℂ) *
        hexUnit (hexCSHeadingFin h0).val := by
      unfold halfStep
      rw [hu]
    _ = (1 / 2 : ℂ) *
        hexUnit (hexAWHeadingMod c
          (hexCSEdgeOfHeading c (hexCSHeadingFin h0))).val := by rw [hm]
    _ = halfStep (hexAWHeading c
        (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) := by
      unfold halfStep
      rw [he]

theorem hexCSHeadingFits_step (c : HexAWCoord) (h : Fin 6) (t : ℤ)
    (hfit : HexCSHeadingFits c h) (ht : t = 1 ∨ t = -1) :
    HexCSHeadingFits
      (hexAWNeighbor c (hexCSEdgeOfHeading c h))
      (hexHeadingTurn h t) := by
  rcases c with ⟨i, j, color⟩
  rcases ht with rfl | rfl <;> cases color <;> fin_cases h <;>
    simp [HexCSHeadingFits, hexCSEdgeOfHeading, hexAWNeighbor,
      hexHeadingTurn] at hfit ⊢


end
end StatMech.Universality
