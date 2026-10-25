/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusContractibleLoop
import Def.StatisticalMechanics.Code.Onsager.TorusLoopCharacter


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_neg_one_zpow_eq_parity (m : ℤ) :
    (-1 : ℂ) ^ m = (-1 : ℂ) ^ (ons_intParity m).val := by
  by_cases hm : Even m
  · rw [hm.neg_one_zpow]
    simp [ons_intParity, hm]
  · have hodd : Odd m := Int.not_even_iff_odd.mp hm
    rw [hodd.neg_one_zpow]
    simp [ons_intParity, hm]

end StatMech.Onsager
