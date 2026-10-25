/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge


namespace StatMech.FrontierD

noncomputable section

theorem intervalIntegral_sixVertexFiniteRootDensity_boundary_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
    ∫ x in p (Fin.last n) - 2 * Real.pi..p 0,
        sixVertexFiniteRootDensity c N (n + 1) p x =
      (2 * (r : Real) + 1) / N := by
  rw [intervalIntegral_sixVertexFiniteRootDensity_boundary hc hN hsol]
  have hchargeReal : (N : Real) = 2 * (n + 1 : Real) + 2 * r := by
    exact_mod_cast hcharge
  rw [hchargeReal]
  ring

theorem sixVertexCyclicRootPartition_densityMass_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
    ∀ k < n + 1,
      ∫ x in sixVertexCyclicRootPartition p k..
          sixVertexCyclicRootPartition p (k + 1),
          sixVertexFiniteRootDensity c N (n + 1) p x =
        if k = 0 then (2 * (r : Real) + 1) / N else 1 / N := by
  intro k hk
  cases k with
  | zero =>
      rw [sixVertexCyclicRootPartition_zero,
        sixVertexCyclicRootPartition_succ p (Nat.zero_le n), if_pos rfl]
      exact intervalIntegral_sixVertexFiniteRootDensity_boundary_fixedCharge
        hc hN hcharge hsol
  | succ j =>
      have hj : j < n := by omega
      let jf : Fin n := ⟨j, hj⟩
      rw [sixVertexCyclicRootPartition_succ p (by omega),
        sixVertexCyclicRootPartition_succ p (by omega), if_neg (by omega)]
      simpa [jf] using intervalIntegral_sixVertexFiniteRootDensity_adjacent
        hc hN hsol jf

theorem sixVertexBetheSolution_boundarySpacing_upper_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) :
    p 0 - (p (Fin.last n) - 2 * Real.pi) ≤
      (2 * (r : Real) + 1) / ((N : Real) * lower) := by
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
  rw [intervalIntegral_sixVertexFiniteRootDensity_boundary_fixedCharge
    hc hN hcharge hsol] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  change p 0 - a ≤ _
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  calc
    (p 0 - a) * ((N : Real) * lower) =
        (N : Real) * ((p 0 - a) * lower) := by ring
    _ ≤ (N : Real) * ((2 * (r : Real) + 1) / N) := hmul
    _ = 2 * (r : Real) + 1 := by field_simp [hNreal.ne']

theorem sixVertexCyclicRootPartition_mesh_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) :
    ∀ k < n + 1,
      sixVertexCyclicRootPartition p (k + 1) -
          sixVertexCyclicRootPartition p k ≤
        (2 * (r : Real) + 1) / ((N : Real) * lower) := by
  intro k hk
  cases k with
  | zero =>
      rw [sixVertexCyclicRootPartition_zero,
        sixVertexCyclicRootPartition_succ p (Nat.zero_le n)]
      exact sixVertexBetheSolution_boundarySpacing_upper_fixedCharge
        hc hN hcharge hopen hsol hlower hdensity
  | succ j =>
      have hj : j < n := by omega
      let jf : Fin n := ⟨j, hj⟩
      rw [sixVertexCyclicRootPartition_succ p (by omega),
        sixVertexCyclicRootPartition_succ p (by omega)]
      have hadj :=
        sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower
          hc hN hopen hsol hlower hdensity jf
      have hNreal : 0 < (N : Real) := by exact_mod_cast hN
      have hden : 0 < (N : Real) * lower := mul_pos hNreal hlower
      simpa [jf] using hadj.trans
        ((div_le_div_iff_of_pos_right hden).2 (by
          norm_num))

theorem abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {mesh : Real}
    (hmesh : ∀ k < n + 1,
      sixVertexCyclicRootPartition p (k + 1) -
          sixVertexCyclicRootPartition p k ≤ mesh)
    {f : Real → Real} {C : NNReal} {F : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hfBound : ∀ x, |f x| ≤ F) :
    |∑ k ∈ Finset.range (n + 1),
          (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) -
        ∫ x in sixVertexCyclicRootPartition p 0..
            sixVertexCyclicRootPartition p (n + 1),
          f x * sixVertexFiniteRootDensity c N (n + 1) p x| ≤
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
          mesh * (2 * Real.pi) +
        (2 * (r : Real) / N) * F := by
  let a := sixVertexCyclicRootPartition p
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  let mass : Nat → Real := fun k =>
    if k = 0 then (2 * (r : Real) + 1) / N else 1 / N
  let U := ∑ k ∈ Finset.range (n + 1), (1 / (N : Real)) * f (a k)
  let W := ∑ k ∈ Finset.range (n + 1), mass k * f (a k)
  let I := ∫ x in a 0..a (n + 1), f x * rho x
  have hcount : n + 1 ≤ N := by omega
  have hB : 0 ≤ sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hquad : |W - I| ≤
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
        mesh * (2 * Real.pi) := by
    have h := abs_weightedLeftEndpointSum_sub_densityIntegral_le
      hf hlip (continuous_sixVertexFiniteRootDensity hc N (n + 1) p) hB
      a mass (n + 1) (sixVertexCyclicRootPartition_ordered hopen) hmesh
      (fun x => abs_sixVertexFiniteRootDensity_le hc hN hcount p x)
      (sixVertexCyclicRootPartition_densityMass_fixedCharge
        hc hN hcharge hsol)
    have hspan : a (n + 1) - a 0 = 2 * Real.pi := by
      dsimp [a]
      rw [sixVertexCyclicRootPartition_end]
      ring
    simpa [W, I, hspan] using h
  have hWU : W = U + (2 * (r : Real) / N) * f (a 0) := by
    dsimp [W, U, mass]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, if_pos]
    ring
  have hcorr : |(2 * (r : Real) / N) * f (a 0)| ≤
      (2 * (r : Real) / N) * F := by
    have hcoef : 0 ≤ 2 * (r : Real) / N := by positivity
    rw [abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left (hfBound (a 0)) hcoef
  change |U - I| ≤ _
  rw [hWU] at hquad
  calc
    |U - I| = |(U + (2 * (r : Real) / N) * f (a 0) - I) -
        (2 * (r : Real) / N) * f (a 0)| := by ring_nf
    _ = |(U + (2 * (r : Real) / N) * f (a 0) - I) +
        (-(2 * (r : Real) / N) * f (a 0))| := by ring_nf
    _ ≤ |U + (2 * (r : Real) / N) * f (a 0) - I| +
        |-(2 * (r : Real) / N) * f (a 0)| := abs_add_le _ _
    _ = |U + (2 * (r : Real) / N) * f (a 0) - I| +
        |(2 * (r : Real) / N) * f (a 0)| := by
      congr 1
      rw [show -(2 * (r : Real) / N) * f (a 0) =
        -((2 * (r : Real) / N) * f (a 0)) by ring, abs_neg]
    _ ≤ (C : Real) * sixVertexFiniteRootDensityUniformBound c *
          mesh * (2 * Real.pi) + (2 * (r : Real) / N) * F :=
      add_le_add hquad hcorr

end
end StatMech.FrontierD
