/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheKernelQuadrature
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSymmetricScatteringBoundaryIncrement_eq
    {c : Real} (hc : 2 < c) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) 0) :
    sixVertexSymmetricScatteringBoundaryIncrement c x =
      4 * Real.arctan
        ((-Real.sin x) /
          (2 * sixVertexAnisotropyMagnitude c *
            (Real.cos x + sixVertexAnisotropyMagnitude c))) := by
  let d := sixVertexAnisotropyMagnitude c
  let D0 := Real.cos x + 1 + 2 * d
  let Dp := Real.cos x - 1 + 2 * d
  let a := Real.sin x / D0
  let b := Real.sin x / Dp
  let r := (-Real.sin x) / (2 * d * (Real.cos x + d))
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hsin : Real.sin x ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1
  have hD0 : 0 < D0 := by
    dsimp [D0]
    linarith [Real.neg_one_le_cos x]
  have hDp : 0 < Dp := by
    dsimp [Dp]
    linarith [Real.neg_one_le_cos x]
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hsin hD0.le
  have hb : b ≤ 0 := div_nonpos_of_nonpos_of_nonneg hsin hDp.le
  have hphase0 : sixVertexSymmetricScatteringPhase c x 0 =
      -2 * x + 4 * Real.arctan a := by
    unfold sixVertexSymmetricScatteringPhase sixVertexTheta
      sixVertexThetaDenominator
    dsimp [a, D0, d, sixVertexAnisotropyMagnitude]
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_neg, Real.cos_neg,
      sub_zero]
    rw [show (-Real.sin x) /
        (Real.cos x + 1 - 2 * sixVertexDelta c) =
          -(Real.sin x /
            (Real.cos x + 1 - 2 * sixVertexDelta c)) by ring,
      Real.arctan_neg]
    ring
  have hphasePi : sixVertexSymmetricScatteringPhase c x (-Real.pi) =
      -2 * x + 4 * Real.arctan b := by
    unfold sixVertexSymmetricScatteringPhase sixVertexTheta
      sixVertexThetaDenominator
    dsimp [b, Dp, d, sixVertexAnisotropyMagnitude]
    simp only [Real.sin_neg, Real.sin_pi, neg_zero, Real.cos_neg,
      Real.cos_pi, sub_zero]
    rw [show (-Real.sin x) /
        (Real.cos x + -1 - 2 * sixVertexDelta c) =
          -(Real.sin x /
            (Real.cos x + -1 - 2 * sixVertexDelta c)) by ring,
      Real.arctan_neg]
    ring
  have hatan : Real.arctan a - Real.arctan b = Real.arctan r := by
    have hadd := Real.arctan_add (x := a) (y := -b) (by nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb])
    rw [Real.arctan_neg] at hadd
    have htrig := Real.sin_sq_add_cos_sq x
    have habpos : 0 < 1 - a * -b := by
      have : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos ha hb
      nlinarith
    have hcd : 0 < Real.cos x + d := by
      linarith [Real.neg_one_le_cos x]
    have habDiff : a - b =
        (-2 * Real.sin x) / (D0 * Dp) := by
      dsimp [a, b]
      field_simp [hD0.ne', hDp.ne']
      dsimp [D0, Dp]
      ring
    have habOne : 1 + a * b =
        (D0 * Dp + Real.sin x ^ 2) / (D0 * Dp) := by
      dsimp [a, b]
      field_simp [hD0.ne', hDp.ne']
    have hdenid : D0 * Dp + Real.sin x ^ 2 =
        4 * d * (Real.cos x + d) := by
      dsimp [D0, Dp]
      nlinarith [htrig]
    have hrational : (a + -b) / (1 - a * -b) = r := by
      rw [show a + -b = a - b by ring,
        show 1 - a * -b = 1 + a * b by ring,
        habDiff, habOne, hdenid]
      dsimp [r]
      field_simp [hD0.ne', hDp.ne', hd.ne', hcd.ne']
      ring
    rw [hrational] at hadd
    exact hadd
  unfold sixVertexSymmetricScatteringBoundaryIncrement
  rw [hphase0, hphasePi]
  calc
    -2 * x + 4 * Real.arctan a - (-2 * x + 4 * Real.arctan b) =
        4 * (Real.arctan a - Real.arctan b) := by ring
    _ = 4 * Real.arctan r := by rw [hatan]
    _ = 4 * Real.arctan
        ((-Real.sin x) /
          (2 * sixVertexAnisotropyMagnitude c *
            (Real.cos x + sixVertexAnisotropyMagnitude c))) := by rfl

end
end StatMech.FrontierD
