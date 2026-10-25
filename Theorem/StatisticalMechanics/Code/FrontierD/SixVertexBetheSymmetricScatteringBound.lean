/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheKernelQuadrature
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexSymmetricScatteringPhase_right
    {c : Real} (hc : 2 < c) (x y : Real) :
    HasDerivAt (sixVertexSymmetricScatteringPhase c x)
      (sixVertexSymmetricScatteringDerivative c x y) y := by
  unfold sixVertexSymmetricScatteringPhase
    sixVertexSymmetricScatteringDerivative
  exact (hasDerivAt_sixVertexTheta_right hc x y).sub
    (hasDerivAt_sixVertexTheta_right hc (-x) y)

theorem continuous_sixVertexSymmetricScatteringDerivative
    {c : Real} (hc : 2 < c) (x : Real) :
    Continuous (sixVertexSymmetricScatteringDerivative c x) := by
  unfold sixVertexSymmetricScatteringDerivative
  apply Continuous.sub
  · apply Continuous.div continuous_const
    · unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      fun_prop
    · intro y
      exact (sixVertexThetaDerivativeDenominator_pos hc x y).ne'
  · apply Continuous.div continuous_const
    · unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      fun_prop
    · intro y
      exact (sixVertexThetaDerivativeDenominator_pos hc (-x) y).ne'

theorem abs_sixVertexThetaRightDerivative_sub_le
    {c : Real} (hc : 2 < c) (x y z : Real) :
    |(-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y) -
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x z)| ≤
      sixVertexThetaLeftKernelLipschitzBound c * |y - z| := by
  have h := sixVertexRootDensityKernel_div_weight_lipschitz hc x y z
  rw [sixVertexRootDensityKernel_div_weight hc,
    sixVertexRootDensityKernel_div_weight hc] at h
  exact h

theorem lipschitzWith_sixVertexSymmetricScatteringDerivative
    {c : Real} (hc : 2 < c) (x : Real) :
    LipschitzWith (sixVertexSymmetricScatteringLipschitzConstant c)
      (sixVertexSymmetricScatteringDerivative c x) := by
  let L := sixVertexThetaLeftKernelLipschitzBound c
  have hL : 0 ≤ L := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
  have hcoe : (sixVertexSymmetricScatteringLipschitzConstant c : Real) =
      2 * L := by
    change (2 : Real) * (Real.toNNReal L : Real) = 2 * L
    rw [Real.coe_toNNReal] <;> exact hL
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, Real.dist_eq, hcoe]
  unfold sixVertexSymmetricScatteringDerivative
  let A : Real → Real := fun u =>
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
      sixVertexThetaDerivativeDenominator c x u
  let B : Real → Real := fun u =>
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-x) /
      sixVertexThetaDerivativeDenominator c (-x) u
  have hA : |A y - A z| ≤ L * |y - z| :=
    abs_sixVertexThetaRightDerivative_sub_le hc x y z
  have hB : |B y - B z| ≤ L * |y - z| :=
    abs_sixVertexThetaRightDerivative_sub_le hc (-x) y z
  change |(A y - B y) - (A z - B z)| ≤ 2 * L * |y - z|
  calc
    |(A y - B y) - (A z - B z)| =
        |(A y - A z) - (B y - B z)| := by ring_nf
    _ ≤ |A y - A z| + |B y - B z| := abs_sub _ _
    _ ≤ L * |y - z| + L * |y - z| := add_le_add hA hB
    _ = 2 * L * |y - z| := by ring

theorem abs_sixVertexSymmetricScatteringDerivative_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    |sixVertexSymmetricScatteringDerivative c x y| ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) := by
  unfold sixVertexSymmetricScatteringDerivative
  rw [← Real.norm_eq_abs]
  apply (norm_sub_le _ _).trans
  simpa [two_mul] using
    add_le_add
      (norm_sixVertexTheta_rightDerivative_le hc x y)
      (norm_sixVertexTheta_rightDerivative_le hc (-x) y)

theorem intervalIntegral_sixVertexSymmetricScatteringDerivative
    {c : Real} (hc : 2 < c) (x a b : Real) :
    ∫ y in a..b, sixVertexSymmetricScatteringDerivative c x y =
      sixVertexSymmetricScatteringPhase c x b -
        sixVertexSymmetricScatteringPhase c x a := by
  let f := sixVertexSymmetricScatteringPhase c x
  let f' := sixVertexSymmetricScatteringDerivative c x
  have hderiv : deriv f = f' := by
    funext y
    exact (hasDerivAt_sixVertexSymmetricScatteringPhase_right hc x y).deriv
  have hdiff : ∀ y ∈ Set.uIcc a b, DifferentiableAt Real f y := by
    intro y _
    exact (hasDerivAt_sixVertexSymmetricScatteringPhase_right hc x y).differentiableAt
  exact intervalIntegral.integral_deriv_eq_sub' f hderiv hdiff
    (continuous_sixVertexSymmetricScatteringDerivative hc x).continuousOn

end
end StatMech.FrontierD
