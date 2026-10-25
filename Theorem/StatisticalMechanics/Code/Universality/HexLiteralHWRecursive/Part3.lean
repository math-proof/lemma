/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_cut_gt (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (h : lo < hi) : lo < hlhr_cut f up lo hi := by
  classical
  simp only [hlhr_cut]
  split_ifs with hk
  · exact hk
  · exact h

theorem hlhr_cut_le (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (h : lo ≤ hi) : hlhr_cut f up lo hi ≤ hi := by
  classical
  simp only [hlhr_cut]
  split_ifs
  · exact hlhr_lastExtremum_le_hi f up h
  · exact le_rfl


@[simp] theorem hlhr_signed_not (up : Bool) (x : ℝ) :
    hlhr_signed (!up) x = -hlhr_signed up x := by
  cases up <;> simp [hlhr_signed]


end StatMech.Universality
