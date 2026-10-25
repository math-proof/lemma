/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexRegularizedBetheLogNormDerivative
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    HasDerivAt (sixVertexRegularizedBetheLogNormDerivative c epsilon)
      (sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x) x := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let B : Real -> Real := fun y => 2 - 2 * Real.cos y + epsilon
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : 0 < A x := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hB : 0 < B x := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add
      (a ^ 2 + 1) using 1 <;> ring
  have hBderiv : HasDerivAt B (2 * Real.sin x) x := by
    dsimp [B]
    convert (Real.hasDerivAt_cos x).const_mul (-2) |>.const_add
      (2 + epsilon) using 1
    · funext y
      ring
    · ring
  have hreg := ((Real.hasDerivAt_sin x).const_mul (-a)).div hAderiv hA.ne'
  have hsing := (Real.hasDerivAt_sin x).neg.div hBderiv hB.ne'
  unfold sixVertexRegularizedBetheLogNormDerivative
    sixVertexRegularizedBetheLogNormSecondDerivative
  dsimp [a, A, B] at hreg hsing ⊢
  convert hreg.add hsing using 1
  · funext y
    simp only [Pi.add_apply, Pi.div_apply, Pi.neg_apply]
    ring
  · ring

theorem abs_sixVertexRegularizedBetheLogNormSecondDerivative_le
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    |sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x| <=
      sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon := by
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
  have hBbase : epsilon <= B := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hBpos : 0 < B := hepsilon.trans_le hBbase
  have hsinSq : Real.sin x ^ 2 <= 1 := by
    simpa [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (Real.sin x)) zero_le_one).2
        (Real.abs_sin_le_one x)
  have hreg :
      |(-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2) / A ^ 2| <=
        a / d ^ 2 + 2 * a ^ 2 / d ^ 4 := by
    rw [abs_div, abs_pow, abs_of_pos hApos]
    have hnum : |-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2| <=
        a * A + 2 * a ^ 2 := by
      calc
        _ <= |-a * Real.cos x * A| +
            |2 * a ^ 2 * Real.sin x ^ 2| := abs_sub _ _
        _ <= a * A + 2 * a ^ 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos ha,
            abs_of_pos hApos,
            abs_of_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2)
              (sq_nonneg a)), abs_of_nonneg (sq_nonneg (Real.sin x))]
          calc
            a * |Real.cos x| * A + 2 * a ^ 2 * Real.sin x ^ 2 <=
                a * 1 * A + 2 * a ^ 2 * 1 := by
              gcongr
              exact Real.abs_cos_le_one x
            _ = _ := by ring
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    have hA2 : d ^ 4 <= A ^ 2 := by
      nlinarith [sq_nonneg (A - d ^ 2)]
    calc
      |-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2| / A ^ 2 <=
          (a * A + 2 * a ^ 2) / A ^ 2 := by gcongr
      _ = a / A + 2 * a ^ 2 / A ^ 2 := by field_simp [hApos.ne']
      _ <= a / d ^ 2 + 2 * a ^ 2 / d ^ 4 := by gcongr
  have hsing :
      |(-Real.cos x * B + 2 * Real.sin x ^ 2) / B ^ 2| <=
        1 / epsilon + 2 / epsilon ^ 2 := by
    rw [abs_div, abs_pow, abs_of_pos hBpos]
    have hnum : |-Real.cos x * B + 2 * Real.sin x ^ 2| <= B + 2 := by
      calc
        _ <= |-Real.cos x * B| + |2 * Real.sin x ^ 2| := abs_add_le _ _
        _ <= B + 2 := by
          rw [abs_mul, abs_neg, abs_of_pos hBpos, abs_mul,
            abs_of_nonneg (by norm_num : (0 : Real) <= 2),
            abs_of_nonneg (sq_nonneg (Real.sin x))]
          nlinarith [Real.abs_cos_le_one x]
    have heps2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hB2 : epsilon ^ 2 <= B ^ 2 := by nlinarith
    calc
      |-Real.cos x * B + 2 * Real.sin x ^ 2| / B ^ 2 <=
          (B + 2) / B ^ 2 := by gcongr
      _ = 1 / B + 2 / B ^ 2 := by field_simp [hBpos.ne']
      _ <= 1 / epsilon + 2 / epsilon ^ 2 := by gcongr
  unfold sixVertexRegularizedBetheLogNormSecondDerivative
    sixVertexRegularizedBetheLogNormSecondDerivativeBound
  dsimp [a, A, d, B] at hreg hsing ⊢
  calc
    |_ + _| <= |_| + |_| := abs_add_le _ _
    _ <= ((c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
        2 * (c ^ 2 - 1) ^ 2 / (c ^ 2 - 2) ^ 4) +
        (1 / epsilon + 2 / epsilon ^ 2) := add_le_add hreg hsing
    _ = _ := by ring

end
end StatMech.FrontierD
