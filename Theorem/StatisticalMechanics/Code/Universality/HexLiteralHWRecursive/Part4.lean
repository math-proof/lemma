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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_lastExtremum_gt (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    lo < hlhr_lastExtremum f up lo hi := by
  let k := hlhr_lastExtremum f up lo hi
  have hspec := hlhr_lastExtremum_spec f up (le_of_lt hlt)
  have hj := hahead (lo + 1) (by omega) (by omega)
  have hjmax := hspec.2.2 (lo + 1) (by omega) (by omega)
  by_contra hnot
  have hklo := hspec.1
  have hk : hlhr_lastExtremum f up lo hi = lo := by omega
  rw [hk] at hjmax
  linarith


theorem hlhr_cut_eq_lastExtremum (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    hlhr_cut f up lo hi = hlhr_lastExtremum f up lo hi := by
  have hk := hlhr_lastExtremum_gt f up hlt hahead
  simp [hlhr_cut, hk]


theorem hlhr_lastExtremum_strict_after (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) {j : ℕ}
    (hj : hlhr_lastExtremum f up lo hi < j) (hjhi : j ≤ hi) :
    hlhr_signed up (f j) <
      hlhr_signed up (f (hlhr_lastExtremum f up lo hi)) := by
  let k := hlhr_lastExtremum f up lo hi
  have hspec := hlhr_lastExtremum_spec f up (le_of_lt hlt)
  have hjlo : lo ≤ j := by
    have hklo := hlhr_lastExtremum_lo_le f up (le_of_lt hlt)
    omega
  have hle := hspec.2.2 j hjlo hjhi
  apply lt_of_le_of_ne hle
  intro heq
  have hjext : HLHRIsExtremum f up lo hi j := by
    refine ⟨hjlo, hjhi, ?_⟩
    intro m hmlo hmhi
    have hm := hspec.2.2 m hmlo hmhi
    linarith
  exact (hlhr_lastExtremum_is_last f up (le_of_lt hlt) hj hjhi) hjext


theorem hlhr_ahead_next (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) :
    HLHRAhead f (!up) (hlhr_lastExtremum f up lo hi) hi := by
  intro j hj hjhi
  rw [hlhr_signed_not, hlhr_signed_not]
  have hs := hlhr_lastExtremum_strict_after f up hlt hj hjhi
  linarith


end StatMech.Universality
