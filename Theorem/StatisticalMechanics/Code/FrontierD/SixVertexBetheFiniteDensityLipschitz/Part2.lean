/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityFinite
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part2


namespace StatMech.FrontierD

noncomputable section

theorem lipschitzWith_sixVertexFiniteRootDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n <= N) (p : Fin n → Real) :
    LipschitzWith (sixVertexFiniteRootDensityLipschitzConstant c)
      (sixVertexFiniteRootDensity c N n p) := by
  let B := sixVertexThetaLeftKernelLipschitzBound c
  let K : Real → Fin n → Real := fun x k =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
      sixVertexThetaDerivativeDenominator c x (p k)
  have hB : 0 <= B := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hnreal : (n : Real) <= (N : Real) := by exact_mod_cast hn
  have hC : ((sixVertexFiniteRootDensityLipschitzConstant c : NNReal) : Real) =
      B / (2 * Real.pi) := by
    simp only [sixVertexFiniteRootDensityLipschitzConstant,
      Real.coe_toNNReal, B]
    exact max_eq_left (div_nonneg hB (by positivity))
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, Real.dist_eq]
  have hsum :
      |∑ k, K x k - ∑ k, K z k| <=
        (n : Real) * B * |x - z| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k, (K x k - K z k)| <=
          ∑ k, |K x k - K z k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _k : Fin n, B * |x - z| := by
        apply Finset.sum_le_sum
        intro k _
        exact sixVertexThetaLeftKernel_lipschitz hc x z (p k)
      _ = (n : Real) * B * |x - z| := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fin, Nat.cast_ofNat]
        ring
  have hdensity :
      sixVertexFiniteRootDensity c N n p x -
          sixVertexFiniteRootDensity c N n p z =
        ((∑ k, K x k) - ∑ k, K z k) /
          ((N : Real) * (2 * Real.pi)) := by
    unfold sixVertexFiniteRootDensity
    dsimp [K]
    field_simp [hNreal.ne', Real.pi_ne_zero]
    ring
  rw [hdensity, abs_div,
    abs_of_pos (mul_pos hNreal (by positivity : 0 < 2 * Real.pi))]
  rw [div_le_iff₀ (mul_pos hNreal (by positivity : 0 < 2 * Real.pi))]
  rw [hC]
  change |(∑ k, K x k) - ∑ k, K z k| <=
    (sixVertexThetaLeftKernelLipschitzBound c / (2 * Real.pi)) *
      |x - z| * ((N : Real) * (2 * Real.pi))
  calc
    |(∑ k, K x k) - ∑ k, K z k| <=
        (n : Real) * B * |x - z| := hsum
    _ <= (N : Real) * B * |x - z| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnreal hB) (abs_nonneg _)
    _ = (sixVertexThetaLeftKernelLipschitzBound c / (2 * Real.pi)) *
        |x - z| * ((N : Real) * (2 * Real.pi)) := by
      dsimp [B]
      field_simp [Real.pi_ne_zero]


end
end StatMech.FrontierD
