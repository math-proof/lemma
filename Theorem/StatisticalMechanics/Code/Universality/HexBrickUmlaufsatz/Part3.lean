/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part3


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


theorem hexBrickDir_turn_ne_opposite (h : Fin 6) (t : ℤ)
    (ht : t = 1 ∨ t = -1) :
    hexBrickDir (hexHeadingTurn h t) ≠ hexBrickDir h + 2 := by
  rcases ht with rfl | rfl <;> fin_cases h <;>
    decide


theorem hexBrick_local_turn_identity (h : Fin 6) (t : ℤ)
    (ht : t = 1 ∨ t = -1) :
    2 * t + 3 * ons_turnPow (hexBrickDir h)
        (hexBrickDir (hexHeadingTurn h t)) =
      hexBrickTurnPotential (hexHeadingTurn h t) -
        hexBrickTurnPotential h := by
  rcases ht with rfl | rfl <;> fin_cases h <;>
    decide


theorem hexBrick_turn_telescope {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i)) :
    2 * (∑ i, turn i) +
        3 * (∑ i, ons_turnPow (hexBrickDir (heading i))
          (hexBrickDir (heading (i + 1)))) = 0 := by
  have hlocal : ∀ i,
      2 * turn i +
          3 * ons_turnPow (hexBrickDir (heading i))
            (hexBrickDir (heading (i + 1))) =
        hexBrickTurnPotential (heading (i + 1)) -
          hexBrickTurnPotential (heading i) := by
    intro i
    rw [hstep i]
    exact hexBrick_local_turn_identity (heading i) (turn i) (hlegal i)
  calc
    2 * (∑ i, turn i) +
          3 * (∑ i, ons_turnPow (hexBrickDir (heading i))
            (hexBrickDir (heading (i + 1)))) =
        ∑ i, (2 * turn i +
          3 * ons_turnPow (hexBrickDir (heading i))
            (hexBrickDir (heading (i + 1)))) := by
              rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ i, (hexBrickTurnPotential (heading (i + 1)) -
          hexBrickTurnPotential (heading i)) := by
            exact Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      have hreindex :
          (∑ i : Fin n, hexBrickTurnPotential (heading (i + 1))) =
            ∑ i : Fin n, hexBrickTurnPotential (heading i) :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n))
          (fun i => hexBrickTurnPotential (heading i))
      rw [hreindex, sub_self]


end StatMech.Universality
