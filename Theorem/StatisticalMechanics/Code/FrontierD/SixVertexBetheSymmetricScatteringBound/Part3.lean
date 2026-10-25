/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheKernelQuadrature
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSymmetricScatteringBoundaryRatio_le
    {c : Real} (hc : 2 < c) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) 0) :
    0 ≤ (-Real.sin x) /
        (2 * sixVertexAnisotropyMagnitude c *
          (Real.cos x + sixVertexAnisotropyMagnitude c)) ∧
    (-Real.sin x) /
        (2 * sixVertexAnisotropyMagnitude c *
          (Real.cos x + sixVertexAnisotropyMagnitude c)) ≤
      1 / (2 * sixVertexAnisotropyMagnitude c *
        Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1)) := by
  let d := sixVertexAnisotropyMagnitude c
  let s := -Real.sin x
  let t := Real.sqrt (d ^ 2 - 1)
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 ≤ s := neg_nonneg.mpr
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1)
  have hcd : 0 < Real.cos x + d := by
    linarith [Real.neg_one_le_cos x]
  have hrad : 0 < d ^ 2 - 1 := by nlinarith
  have ht : 0 < t := Real.sqrt_pos.2 hrad
  have htSq : t ^ 2 = d ^ 2 - 1 := Real.sq_sqrt hrad.le
  have htrig := Real.sin_sq_add_cos_sq x
  have hsSq : s ^ 2 = 1 - Real.cos x ^ 2 := by
    dsimp [s]
    nlinarith
  have hsq : (s * t) ^ 2 ≤ (Real.cos x + d) ^ 2 := by
    rw [mul_pow, htSq, hsSq]
    nlinarith [sq_nonneg (d * Real.cos x + 1)]
  have hst : s * t ≤ Real.cos x + d :=
    (sq_le_sq₀ (mul_nonneg hs ht.le) hcd.le).1 hsq
  have hratio : s / (Real.cos x + d) ≤ 1 / t := by
    rw [div_le_iff₀ hcd]
    have hdiv := (le_div_iff₀ ht).2 hst
    simpa [one_div, mul_comm] using hdiv
  have htwoD : 0 < 2 * d := by positivity
  constructor
  · dsimp [s, d]
    positivity
  · change s / (2 * d * (Real.cos x + d)) ≤ 1 / (2 * d * t)
    calc
      s / (2 * d * (Real.cos x + d)) =
          (s / (Real.cos x + d)) / (2 * d) := by
        field_simp [hcd.ne', hd.ne']
      _ ≤ (1 / t) / (2 * d) :=
        div_le_div_of_nonneg_right hratio htwoD.le
      _ = 1 / (2 * d * t) := by
        field_simp [ht.ne', hd.ne']

theorem sixVertexSymmetricScatteringBoundaryBound_nonneg
    {c : Real} (hc : 2 < c) :
    0 ≤ sixVertexSymmetricScatteringBoundaryBound c := by
  let d := sixVertexAnisotropyMagnitude c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hsqrt : 0 < Real.sqrt (d ^ 2 - 1) :=
    Real.sqrt_pos.2 (by nlinarith)
  unfold sixVertexSymmetricScatteringBoundaryBound
  exact mul_nonneg (by norm_num)
    (Real.arctan_nonneg.2 (by positivity))

theorem sixVertexSymmetricScatteringBoundaryBound_lt_two_pi
    {c : Real} :
    sixVertexSymmetricScatteringBoundaryBound c < 2 * Real.pi := by
  let z := 1 / (2 * sixVertexAnisotropyMagnitude c *
    Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1))
  have hz := Real.arctan_lt_pi_div_two z
  unfold sixVertexSymmetricScatteringBoundaryBound
  change 4 * Real.arctan z < 2 * Real.pi
  linarith

theorem sixVertexSymmetricScatteringBoundaryIncrement_bounds
    {c : Real} (hc : 2 < c) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) 0) :
    0 ≤ sixVertexSymmetricScatteringBoundaryIncrement c x ∧
      sixVertexSymmetricScatteringBoundaryIncrement c x ≤
        sixVertexSymmetricScatteringBoundaryBound c := by
  rw [sixVertexSymmetricScatteringBoundaryIncrement_eq hc hx]
  have hr := sixVertexSymmetricScatteringBoundaryRatio_le hc hx
  constructor
  · exact mul_nonneg (by norm_num) (Real.arctan_nonneg.2 hr.1)
  · unfold sixVertexSymmetricScatteringBoundaryBound
    exact mul_le_mul_of_nonneg_left
      (Real.arctan_le_arctan_iff.2 hr.2) (by norm_num)

end
end StatMech.FrontierD
