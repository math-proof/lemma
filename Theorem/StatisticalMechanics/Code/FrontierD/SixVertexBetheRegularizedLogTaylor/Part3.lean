/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part3


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexRegularizedBetheLogNormDerivative_le
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    |sixVertexRegularizedBetheLogNormDerivative c epsilon x| <=
      sixVertexRegularizedBetheLogNormDerivativeBound c epsilon := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let d := c ^ 2 - 2
  let B := 2 - 2 * Real.cos x + epsilon
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hA : d ^ 2 <= A := by
    dsimp [A, a, d]
    nlinarith [Real.neg_one_le_cos x]
  have hApos : 0 < A := (sq_pos_of_pos hd).trans_le hA
  have hB : epsilon <= B := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hBpos : 0 < B := hepsilon.trans_le hB
  unfold sixVertexRegularizedBetheLogNormDerivative
    sixVertexRegularizedBetheLogNormDerivativeBound
  dsimp [a, A, d, B]
  calc
    |(-a * Real.sin x / A) - Real.sin x / B| <=
        |-a * Real.sin x / A| + |Real.sin x / B| := abs_sub _ _
    _ <= a / d ^ 2 + 1 / epsilon := by
      rw [abs_div, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos hApos,
        abs_div, abs_of_pos hBpos]
      apply add_le_add
      · calc
          a * |Real.sin x| / A <= a / A := by
            apply div_le_div_of_nonneg_right _ hApos.le
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) ha.le
          _ <= a / d ^ 2 :=
            div_le_div_of_nonneg_left ha.le (sq_pos_of_pos hd) hA
      · calc
          |Real.sin x| / B <= 1 / B := by
            exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) hBpos.le
          _ <= 1 / epsilon :=
            div_le_div_of_nonneg_left zero_le_one hepsilon hB

end
end StatMech.FrontierD
