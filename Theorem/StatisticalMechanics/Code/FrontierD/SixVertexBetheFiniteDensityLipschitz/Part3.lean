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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexFiniteRootDensity_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n <= N) (p : Fin n → Real) (x : Real) :
    |sixVertexFiniteRootDensity c N n p x| <=
      sixVertexFiniteRootDensityUniformBound c := by
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  let K : Fin n → Real := fun k =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
      sixVertexThetaDerivativeDenominator c x (p k)
  have hR : 0 <= R := by
    exact (div_pos
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))).le
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hnreal : (n : Real) <= (N : Real) := by exact_mod_cast hn
  have hsum : |∑ k, K k| <= (N : Real) * R := by
    calc
      |∑ k, K k| <= ∑ k, |K k| := Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _k : Fin n, R := by
        apply Finset.sum_le_sum
        intro k _
        rw [← Real.norm_eq_abs]
        exact norm_sixVertexTheta_leftDerivative_le hc x (p k)
      _ = (n : Real) * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp
      _ <= (N : Real) * R := mul_le_mul_of_nonneg_right hnreal hR
  unfold sixVertexFiniteRootDensity sixVertexFiniteRootDensityUniformBound
  change |(1 + (∑ k, K k) / (N : Real)) / (2 * Real.pi)| <= _
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 <= 2 * Real.pi)
  calc
    |1 + (∑ k, K k) / (N : Real)| <=
        1 + |(∑ k, K k) / (N : Real)| := by
      simpa using abs_add_le (1 : Real) ((∑ k, K k) / (N : Real))
    _ = 1 + |∑ k, K k| / (N : Real) := by
      rw [abs_div, abs_of_pos hNreal]
    _ <= 1 + R := by
      gcongr
      exact (div_le_iff₀ hNreal).2 (by simpa [mul_comm] using hsum)
    _ = 1 + sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by rfl


theorem abs_gap_mul_finiteRootDensity_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n + 1 <= N) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (j : Fin n) :
    |(p j.succ - p j.castSucc) *
          sixVertexFiniteRootDensity c N (n + 1) p (p j.castSucc) -
        1 / N| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (p j.succ - p j.castSucc) ^ 2 := by
  have horder : p j.castSucc <= p j.succ := by
    exact (hopen.1 (by simp)).le
  have hquad := abs_gap_mul_left_sub_intervalIntegral_le
    (continuous_sixVertexFiniteRootDensity hc N (n + 1) p)
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hn p) horder
  rw [intervalIntegral_sixVertexFiniteRootDensity_adjacent
    hc hN hsol j] at hquad
  exact hquad


theorem abs_gap_mul_finiteRootDensity_right_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n + 1 <= N) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (j : Fin n) :
    |(p j.succ - p j.castSucc) *
          sixVertexFiniteRootDensity c N (n + 1) p (p j.succ) -
        1 / N| <=
      2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (p j.succ - p j.castSucc) ^ 2 := by
  let gap := p j.succ - p j.castSucc
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  have hgap : 0 <= gap := sub_nonneg.mpr (hopen.1 (by simp)).le
  have hleft := abs_gap_mul_finiteRootDensity_sub_inv_width_le
    hc hN hn hopen hsol j
  have hlip := lipschitzWith_sixVertexFiniteRootDensity hc hN hn p
  have hrho : |rho (p j.succ) - rho (p j.castSucc)| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap := by
    calc
      |rho (p j.succ) - rho (p j.castSucc)| =
          dist (rho (p j.succ)) (rho (p j.castSucc)) := by
            rw [Real.dist_eq]
      _ <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          dist (p j.succ) (p j.castSucc) :=
        hlip.dist_le_mul _ _
      _ = (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap := by
        rw [Real.dist_eq, abs_of_nonneg hgap]
  have hmove :
      |gap * rho (p j.succ) - gap * rho (p j.castSucc)| <=
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hgap]
    nlinarith
  change |gap * rho (p j.succ) - 1 / N| <= _
  calc
    |gap * rho (p j.succ) - 1 / N| <=
        |gap * rho (p j.succ) - gap * rho (p j.castSucc)| +
          |gap * rho (p j.castSucc) - 1 / N| := by
      exact abs_sub_le _ _ _
    _ <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 +
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 :=
      add_le_add hmove hleft
    _ = 2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 := by
      ring


theorem intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n → Real) (a b : Real) :
    ∫ x in a..b, sixVertexFiniteRootDensity c N n p x =
      sixVertexBetheCountingFunction c N n p b -
        sixVertexBetheCountingFunction c N n p a := by
  let f := sixVertexBetheCountingFunction c N n p
  let f' := sixVertexFiniteRootDensity c N n p
  have hderiv : deriv f = f' := by
    funext x
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).deriv
  have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt Real f x := by
    intro x _
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).differentiableAt
  have hcont : ContinuousOn f' (Set.uIcc a b) :=
    (continuous_sixVertexFiniteRootDensity hc N n p).continuousOn
  exact intervalIntegral.integral_deriv_eq_sub' f hderiv hdiff hcont


theorem intervalIntegral_sixVertexFiniteRootDensity_boundary
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin (n + 1) → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
    ∫ x in p (Fin.last n) - 2 * Real.pi..p 0,
        sixVertexFiniteRootDensity c N (n + 1) p x =
      ((N : Real) - 2 * (n + 1 : Real) + 1) / N := by
  let a := p (Fin.last n) - 2 * Real.pi
  have hshift : a + 2 * Real.pi = p (Fin.last n) := by
    dsimp [a]
    ring
  have hperiod := sixVertexBetheCountingFunction_add_two_pi
    hN c p a
  rw [hshift] at hperiod
  have hfirst := sixVertexBetheCountingFunction_at_root
    hN hsol (0 : Fin (n + 1))
  have hlast := sixVertexBetheCountingFunction_at_root
    hN hsol (Fin.last n)
  rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p a (p 0)]
  rw [hfirst]
  have hquantumFirst :
      sixVertexCentralQuantumNumber (0 : Fin (n + 1)) = -(n : Real) / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    simp
    ring
  have hquantumLast :
      sixVertexCentralQuantumNumber (Fin.last n) = (n : Real) / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    simp
    ring
  rw [hquantumFirst]
  rw [hquantumLast] at hlast
  rw [hlast] at hperiod
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hN0 : (N : Real) ≠ 0 := hNreal.ne'
  dsimp [a]
  dsimp [a] at hperiod
  push_cast at hperiod ⊢
  field_simp [hN0] at hperiod ⊢
  linarith

end
end StatMech.FrontierD
