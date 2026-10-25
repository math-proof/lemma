/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part4
import Def.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_spinKacWardAt_iff_coefficientIdentity
    (L : ℕ) [NeZero L] [Fact (2 < L)] (x : ℝ) :
    ons_spinKacWardAt L x ↔ ons_spinCoefficientIdentity L x := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  unfold ons_spinKacWardAt ons_spinCoefficientIdentity
  constructor
  · rintro ⟨h00, h10, h01, h11⟩ a b
    fin_cases a <;> fin_cases b
    · change (ons_spinCharacterSum L x 0 0 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_zero]
      exact_mod_cast h00
    · change (ons_spinCharacterSum L x 0 1 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_one]
      exact_mod_cast h01
    · change (ons_spinCharacterSum L x 1 0 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_zero]
      exact_mod_cast h10
    · change (ons_spinCharacterSum L x 1 1 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_one]
      exact_mod_cast h11
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hh := h 0 0
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_zero] at hh
      exact_mod_cast hh
    · have hh := h 1 0
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_zero] at hh
      exact_mod_cast hh
    · have hh := h 0 1
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_one] at hh
      exact_mod_cast hh
    · have hh := h 1 1
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_one] at hh
      exact_mod_cast hh

end StatMech.Onsager
