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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part5


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_orientedSpan_pos (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    0 < hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
  unfold hlhr_orientedSpan
  exact sub_pos.mpr (hahead _ (hlhr_lastExtremum_gt f up hlt hahead)
    (hlhr_lastExtremum_le_hi f up (le_of_lt hlt)))


theorem hlhr_orientedSpan_next_lt (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi)
    (hk : hlhr_lastExtremum f up lo hi < hi) :
    hlhr_orientedSpan f (!up) (hlhr_lastExtremum f up lo hi)
        (hlhr_lastExtremum f (!up) (hlhr_lastExtremum f up lo hi) hi)
      < hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
  let k := hlhr_lastExtremum f up lo hi
  let l := hlhr_lastExtremum f (!up) k hi
  have hnext := hlhr_ahead_next f up hlt
  have hkl : k < l := hlhr_lastExtremum_gt f (!up) hk hnext
  have hklo : lo < k := by
    dsimp [k]
    exact hlhr_lastExtremum_gt f up hlt hahead
  have hlo_l : lo < l := lt_trans hklo hkl
  have hlhi : l ≤ hi := hlhr_lastExtremum_le_hi f (!up) (le_of_lt hk)
  have hold := hahead l hlo_l hlhi
  unfold hlhr_orientedSpan
  rw [hlhr_signed_not, hlhr_signed_not]
  dsimp [k, l] at hold ⊢
  linarith


end StatMech.Universality
