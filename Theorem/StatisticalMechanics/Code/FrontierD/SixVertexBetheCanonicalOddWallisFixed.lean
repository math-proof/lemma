/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4


namespace StatMech.FrontierD

open Filter Topology Finset MeasureTheory

noncomputable section

theorem abs_mul_cos_sub_sin_le_abs_cube_div_two
    {x : Real} (hx : |x| <= 1) :
    |x * Real.cos x - Real.sin x| <= |x| ^ 3 / 2 := by
  let u := |x|
  have hu0 : 0 <= u := abs_nonneg x
  have hu1 : u <= 1 := hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have huPos : 0 < u := abs_pos.mpr hx0
  have hsinLower : u - u ^ 3 / 4 <= Real.sin u :=
    (Real.sin_gt_sub_cube huPos hu1).le
  have hsinUpper : Real.sin u <= u := Real.sin_le hu0
  have hcosLower : 1 - u ^ 2 / 2 <= Real.cos u :=
    Real.one_sub_sq_div_two_le_cos
  have hcosUpper : Real.cos u <= 1 := Real.cos_le_one u
  have hgUpper : u * Real.cos u - Real.sin u <= u ^ 3 / 2 := by
    nlinarith
  have hgLower : -(u ^ 3 / 2) <=
      u * Real.cos u - Real.sin u := by
    nlinarith
  have habs : |u * Real.cos u - Real.sin u| <= u ^ 3 / 2 :=
    (abs_le).2 ⟨hgLower, hgUpper⟩
  rcases le_total 0 x with hxPos | hxNeg
  · simpa [u, abs_of_nonneg hxPos] using habs
  · have habs' : |(-x) * Real.cos (-x) - Real.sin (-x)| <=
        (-x) ^ 3 / 2 := by
      simpa [u, abs_of_nonpos hxNeg] using habs
    calc
      |x * Real.cos x - Real.sin x| =
          |(-x) * Real.cos (-x) - Real.sin (-x)| := by
        rw [Real.cos_neg, Real.sin_neg]
        rw [show (-x) * Real.cos x - -Real.sin x =
          -(x * Real.cos x - Real.sin x) by ring, abs_neg]
      _ <= (-x) ^ 3 / 2 := habs'
      _ = |x| ^ 3 / 2 := by rw [abs_of_nonpos hxNeg]

theorem abs_sixVertexSincDerivative_le_abs_div_two
    {x : Real} (hx : |x| <= 1) :
    |sixVertexSincDerivative x| <= |x| / 2 := by
  by_cases hx0 : x = 0
  · simp [sixVertexSincDerivative, hx0]
  rw [sixVertexSincDerivative, if_neg hx0, abs_div, abs_pow]
  have hnum := abs_mul_cos_sub_sin_le_abs_cube_div_two hx
  have hxabs : 0 < |x| := abs_pos.mpr hx0
  calc
    |x * Real.cos x - Real.sin x| / |x| ^ 2 <=
        (|x| ^ 3 / 2) / |x| ^ 2 := by gcongr
    _ = |x| / 2 := by field_simp [hxabs.ne']

theorem continuousAt_sixVertexSincDerivative_zero :
    ContinuousAt sixVertexSincDerivative 0 := by
  rw [ContinuousAt, show sixVertexSincDerivative 0 = 0 by
    simp [sixVertexSincDerivative]]
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hdelta : 0 < min 1 (2 * epsilon) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : Real) hdelta] with x hx
  rw [Metric.mem_ball, Real.dist_eq] at hx
  simp only [sub_zero] at hx
  have hxOne : |x| <= 1 := (lt_min_iff.mp hx).1.le
  have hxEps : |x| / 2 < epsilon := by
    have := (lt_min_iff.mp hx).2
    linarith
  rw [Real.dist_eq, sub_zero]
  exact (abs_sixVertexSincDerivative_le_abs_div_two hxOne).trans_lt hxEps

theorem continuous_sixVertexSincDerivative :
    Continuous sixVertexSincDerivative := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa [hx] using continuousAt_sixVertexSincDerivative_zero
  · have hquot : ContinuousAt
        (fun y : Real => (y * Real.cos y - Real.sin y) / y ^ 2) x := by
      exact ((continuousAt_id.mul Real.continuous_cos.continuousAt).sub
        Real.continuous_sin.continuousAt).div (continuousAt_id.pow 2)
          (pow_ne_zero 2 hx)
    apply hquot.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [sixVertexSincDerivative, hy]

end
end StatMech.FrontierD
