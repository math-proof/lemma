/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthSubcritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthSubcritical


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhds_hexChiE_lt_one : hexChiE < 1 := by
  unfold hexChiE
  rw [div_lt_one hex_sqrt_pos]
  calc
    (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt (2 + Real.sqrt 2) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      have hs := Real.sqrt_nonneg 2
      linarith


theorem hlhds_summable_of_local
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
    ∀ x, 0 < x → x < hexChiE →
      Summable (fun n => hlc_sawCountR hexAWStart 1 n * x ^ n) := by
  intro x hx hxchi
  apply HLHDTaggedTwoHalfData.summable_of_taggedTwoHalfData
    (fun N => hlhds_twoHalfData N)
    hx (le_of_lt (lt_trans hxchi hlhds_hexChiE_lt_one)) hxchi
  · intro T hT L
    exact hlocal T L hT
  · intro T hT L
    exact hexCS_boundaryWindowLaw T L hT

end
end StatMech.Universality
