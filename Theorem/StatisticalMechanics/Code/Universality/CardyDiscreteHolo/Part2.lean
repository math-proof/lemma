/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part2


namespace StatMech.Universality

open Complex


@[simp] theorem cardyWpow_zero : cardyWpow 0 = 1 := by simp [cardyWpow]

@[simp] theorem cardyWpow_one : cardyWpow 1 = cardyOmega := by
  show cardyOmega ^ (1 : ZMod 3).val = cardyOmega
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]

@[simp] theorem cardyWpow_two : cardyWpow 2 = cardyOmega ^ 2 := by
  show cardyOmega ^ (2 : ZMod 3).val = cardyOmega ^ 2
  rw [show (2 : ZMod 3).val = 2 from rfl]


theorem cardyWpow_succ (k : ZMod 3) : cardyWpow (k + 1) = cardyOmega * cardyWpow k := by
  fin_cases k
  · show cardyWpow ((0 : ZMod 3) + 1) = cardyOmega * cardyWpow (0 : ZMod 3)
    rw [show ((0 : ZMod 3) + 1) = 1 from rfl, cardyWpow_one, cardyWpow_zero]; ring
  · show cardyWpow ((1 : ZMod 3) + 1) = cardyOmega * cardyWpow (1 : ZMod 3)
    rw [show ((1 : ZMod 3) + 1) = 2 from rfl, cardyWpow_two, cardyWpow_one]; ring
  · show cardyWpow ((2 : ZMod 3) + 1) = cardyOmega * cardyWpow (2 : ZMod 3)
    rw [show ((2 : ZMod 3) + 1) = 0 from rfl, cardyWpow_zero, cardyWpow_two]
    rw [show cardyOmega * cardyOmega ^ 2 = cardyOmega ^ 3 by ring, cardyOmega_cube]


theorem cardyWpow_sum_zero : cardyWpow 0 + cardyWpow 1 + cardyWpow 2 = 0 := by
  rw [cardyWpow_zero, cardyWpow_one, cardyWpow_two]; exact cardyOmega_sum_zero


end StatMech.Universality
