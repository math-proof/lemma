/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedDensityCauchy
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Mathlib.Algebra.Field.Periodic


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFiniteRootDensity_lower_of_weighted_close
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    {rho : Real → Real} {rhoLower eta : Real}
    (hrhoLower : ∀ x, rhoLower ≤ rho x)
    (hclose : ∀ x,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ eta) :
    ∀ x, rhoLower -
        eta / ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) ≤
      sixVertexFiniteRootDensity c N n p x := by
  intro x
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hw := sixVertexRootDensityWeight_lower hc x
  have hweight := sixVertexRootDensityWeight_pos hc x
  have hdiff :
      |sixVertexFiniteRootDensity c N n p x - rho x| ≤ eta / wmin := by
    have heta : 0 ≤ eta := le_trans (abs_nonneg _) (hclose x)
    have hcx := hclose x
    apply (le_div_iff₀ hwmin).2
    calc
      |sixVertexFiniteRootDensity c N n p x - rho x| * wmin ≤
          sixVertexRootDensityWeight c x *
            |sixVertexFiniteRootDensity c N n p x - rho x| :=
        by simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hw (abs_nonneg
            (sixVertexFiniteRootDensity c N n p x - rho x))
      _ = |sixVertexRootDensityWeight c x *
          (sixVertexFiniteRootDensity c N n p x - rho x)| := by
        rw [abs_mul, abs_of_pos hweight]
      _ ≤ eta := hcx
  have hlower := hrhoLower x
  rw [abs_le] at hdiff
  change rhoLower - eta / wmin ≤ _
  linarith

theorem sixVertexFiniteRootDensity_lower_at_of_weighted_close
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    {rho : Real → Real} {rhoLower eta x : Real}
    (hrhoLower : rhoLower ≤ rho x)
    (hclose :
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ eta) :
    rhoLower - eta /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) ≤
      sixVertexFiniteRootDensity c N n p x := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hw := sixVertexRootDensityWeight_lower hc x
  have hweight := sixVertexRootDensityWeight_pos hc x
  have hdiff :
      |sixVertexFiniteRootDensity c N n p x - rho x| ≤ eta / wmin := by
    have heta : 0 ≤ eta := le_trans (abs_nonneg _) hclose
    apply (le_div_iff₀ hwmin).2
    calc
      |sixVertexFiniteRootDensity c N n p x - rho x| * wmin ≤
          sixVertexRootDensityWeight c x *
            |sixVertexFiniteRootDensity c N n p x - rho x| :=
        by simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hw (abs_nonneg
            (sixVertexFiniteRootDensity c N n p x - rho x))
      _ = |sixVertexRootDensityWeight c x *
          (sixVertexFiniteRootDensity c N n p x - rho x)| := by
        rw [abs_mul, abs_of_pos hweight]
      _ ≤ eta := hclose
  rw [abs_le] at hdiff
  change rhoLower - eta / wmin ≤ _
  linarith

theorem sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) (j : Fin n) :
    p j.succ - p j.castSucc ≤ 1 / ((N : Real) * lower) := by
  have horder : p j.castSucc ≤ p j.succ := (hopen.1 (by simp)).le
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N (n + 1) p).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_adjacent hc hN hsol j] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith

theorem sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) :
    p 0 - (p (Fin.last n) - 2 * Real.pi) ≤
      1 / ((N : Real) * lower) := by
  let a := p (Fin.last n) - 2 * Real.pi
  have horder : a ≤ p 0 := by
    have hfirst := (hopen.2.2 (0 : Fin (n + 1))).1
    have hlast := (hopen.2.2 (Fin.last n)).2
    dsimp [a]
    linarith [Real.pi_pos]
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N (n + 1) p).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hboundary := intervalIntegral_sixVertexFiniteRootDensity_boundary
    hc hN hsol
  have hmass : ((N : Real) - 2 * (n + 1 : Real) + 1) / N =
      1 / (N : Real) := by
    have hhalfReal : (N : Real) = 2 * (n + 1 : Real) := by exact_mod_cast hhalf
    rw [hhalfReal]
    ring
  rw [hboundary, hmass] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  change p 0 - a ≤ 1 / ((N : Real) * lower)
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith

theorem sixVertexCyclicRootPartition_mesh_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) :
    ∀ k < n + 1,
      sixVertexCyclicRootPartition p (k + 1) -
          sixVertexCyclicRootPartition p k ≤
        1 / ((N : Real) * lower) := by
  intro k hk
  cases k with
  | zero =>
      rw [sixVertexCyclicRootPartition_zero,
        sixVertexCyclicRootPartition_succ p (Nat.zero_le n)]
      exact sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower
        hc hN hhalf hopen hsol hlower hdensity
  | succ j =>
      have hj : j < n := by omega
      let jf : Fin n := ⟨j, hj⟩
      rw [sixVertexCyclicRootPartition_succ p (by omega),
        sixVertexCyclicRootPartition_succ p (by omega)]
      simpa [jf] using
        sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower
          hc hN hopen hsol hlower hdensity jf


theorem abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : 0 < n)
    (hhalf : N = 2 * n) {p : Fin n → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N n p x)
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) :
    |(∑ j, f (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c N n p y| ≤
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
        (1 / ((N : Real) * lower)) * (2 * Real.pi) := by
  cases n with
  | zero => omega
  | succ n =>
      have hcount : n + 1 ≤ N := by omega
      have hmesh := sixVertexCyclicRootPartition_mesh_of_finiteDensityLower
        hc hN hhalf hopen hsol hlower hdensity
      have hquad := abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_of_mesh
        hc hN hcount hhalf hopen hsol hmesh hf hlip
      have hsum := sum_cyclicRootPartition_eq_sum_roots_of_periodic p hperiodic
      have hsumScaled :
          ∑ k ∈ Finset.range (n + 1),
              (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) =
            (∑ j, f (p j)) / N := by
        rw [← Finset.mul_sum, hsum]
        ring
      have hint := intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle
        (N := N) c p hperiodic
      rw [hsumScaled, hint] at hquad
      exact hquad

end
end StatMech.FrontierD
