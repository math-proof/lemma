/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterZeroFieldSheet
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBondUpper.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBridgeVariance


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem twoBridgeTiltVariance_le_neg
    {t A E : Real} (ht0 : 0 <= t) (ht1 : t < 1)
    (hA0 : 0 <= A) (hE0 : 0 <= E) (hE1 : E <= 1)
    (hAE : A <= 1 + E) :
    twoBridgeTiltVariance t A E <= twoBridgeTiltVariance (-t) A E := by
  let Pp := 1 + A * t + E * t ^ 2
  let Pm := 1 - A * t + E * t ^ 2
  let B := A ^ 2 * E * t ^ 4 - A ^ 2 - E ^ 3 * t ^ 4 -
    3 * E ^ 2 * t ^ 4 + 2 * E ^ 2 * t ^ 2 -
    2 * E * t ^ 2 + 3 * E + 1
  have ht1' : t <= 1 := ht1.le
  have hB : 0 <= B := by
    exact twoBridgeVarianceSkewPolynomial_nonneg ht0 ht1' hA0 hE0 hE1 hAE
  have hPp : 0 < Pp := by
    dsimp [Pp]
    positivity
  have hEtlt : E * t < 1 := by
    exact (mul_le_of_le_one_left ht0 hE1).trans_lt ht1
  have hlower : (1 - t) * (1 - E * t) <= Pm := by
    dsimp [Pm]
    have hm := mul_le_mul_of_nonneg_right hAE ht0
    nlinarith [mul_nonneg hE0 (sq_nonneg t)]
  have hPmlower : 0 < (1 - t) * (1 - E * t) :=
    mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hEtlt)
  have hPm : 0 < Pm := hPmlower.trans_le hlower
  have htquad : 0 <= 1 - t ^ 2 := by nlinarith [sq_nonneg t]
  have htop : 0 <= 4 * A * t * (1 - t ^ 2) * B := by positivity
  have hdiff :
      twoBridgeTiltVariance (-t) A E -
          twoBridgeTiltVariance t A E =
        (4 * A * t * (1 - t ^ 2) * B) / (Pm ^ 2 * Pp ^ 2) := by
    unfold twoBridgeTiltVariance
    simp only [neg_sq, mul_neg, neg_mul]
    rw [show 1 + -(A * t) + E * t ^ 2 = Pm by
      dsimp [Pm]; ring]
    rw [show 1 + A * t + E * t ^ 2 = Pp by rfl]
    field_simp [hPp.ne', hPm.ne']
    dsimp [B]
    ring
  apply sub_nonneg.mp
  rw [hdiff]
  exact div_nonneg htop (mul_nonneg (sq_nonneg Pm) (sq_nonneg Pp))

end
end StatMech.Ising
