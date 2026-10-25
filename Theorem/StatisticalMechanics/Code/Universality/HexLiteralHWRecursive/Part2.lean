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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_lastExtremum_spec (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) :
    HLHRIsExtremum f up lo hi (hlhr_lastExtremum f up lo hi) := by
  classical
  unfold hlhr_lastExtremum
  rw [dif_pos hlo]
  obtain ⟨k, hk⟩ := hlhr_exists_extremum f up hlo
  exact Nat.findGreatest_spec hk.2.1 hk

theorem hlhr_lastExtremum_lo_le (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) : lo ≤ hlhr_lastExtremum f up lo hi :=
  (hlhr_lastExtremum_spec f up hlo).1

theorem hlhr_lastExtremum_le_hi (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) : hlhr_lastExtremum f up lo hi ≤ hi :=
  (hlhr_lastExtremum_spec f up hlo).2.1


theorem hlhr_lastExtremum_is_last (f : ℕ → ℝ) (up : Bool)
    {lo hi j : ℕ} (hlo : lo ≤ hi)
    (hj : hlhr_lastExtremum f up lo hi < j) (hjhi : j ≤ hi) :
    ¬ HLHRIsExtremum f up lo hi j := by
  classical
  unfold hlhr_lastExtremum at hj
  rw [dif_pos hlo] at hj
  exact Nat.findGreatest_is_greatest hj hjhi


end StatMech.Universality
