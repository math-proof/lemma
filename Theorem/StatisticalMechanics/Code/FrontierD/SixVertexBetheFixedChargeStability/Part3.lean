/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeStability.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div
    (c lower : Real) (r : Nat) {N : Nat} (hN : 0 < N) :
    sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower =
      sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N := by
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sixVertexFixedChargeDensityStabilityErrorOfLower
    sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
  field_simp [hN0]
  ring

theorem exists_uniformBound_sixVertexFixedChargeDensityStabilityError_Ici
    {a lower : Real} (ha : 2 < a) (hlower : 0 < lower) (r : Nat) :
    ∃ B : Real, 0 < B ∧ ∀ {N : Nat}, 0 < N → ∀ c, a ≤ c →
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower ≤ B / N := by
  obtain ⟨kernelB, _thetaB, R, _boundaryB, hkernelB, _hthetaB, hR,
      _hboundaryB, hcoeff⟩ :=
    exists_uniform_sixVertexCoefficientBounds_Ici ha
  let B :=
    ((r : Real) / (2 * Real.pi)) * (2 * R) +
    ((r : Real) / (2 * Real.pi)) * (2 * R ^ 2) +
    (kernelB * ((1 + R) / (2 * Real.pi)) *
          ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
        (2 * (r : Real)) * (2 * R ^ 2)) / (2 * Real.pi)
  have hRone : 1 ≤ R := by
    have haRatio := (hcoeff a le_rfl).2.2.1
    have hd := one_lt_sixVertexAnisotropyMagnitude ha
    have hone : 1 ≤ sixVertexAnisotropyMagnitude a /
        (sixVertexAnisotropyMagnitude a - 1) := by
      rw [le_div_iff₀ (sub_pos.mpr hd)]
      linarith
    exact hone.trans haRatio
  have hB : 0 < B := by
    dsimp [B]
    have hpi := Real.pi_pos
    have hrterm : 0 ≤ (r : Real) := by positivity
    have hlast : 0 < kernelB * ((1 + R) / (2 * Real.pi)) *
          ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) := by
      positivity
    positivity
  refine ⟨B, hB, ?_⟩
  intro N hN c hac
  rw [sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div
    c lower r hN]
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  apply div_le_div_of_nonneg_right _ hNreal.le
  obtain ⟨hkernel, _htheta, hratio, _hboundary⟩ := hcoeff c hac
  have hc : 2 < c := ha.trans_le hac
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  have hs := sixVertexRootDensityScale_pos hc
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hratio0 : 0 ≤ sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1) := by positivity
  have hweight0 : 0 ≤ (sixVertexAnisotropyMagnitude c + 1) /
      sixVertexRootDensityScale c := by positivity
  have hweight : (sixVertexAnisotropyMagnitude c + 1) /
      sixVertexRootDensityScale c ≤ 2 * R := by
    calc
      (sixVertexAnisotropyMagnitude c + 1) /
          sixVertexRootDensityScale c ≤
        (sixVertexAnisotropyMagnitude c + 1) /
          (sixVertexAnisotropyMagnitude c - 1) := by
            exact div_le_div_of_nonneg_left (by positivity)
              (sub_pos.mpr hd)
              (sixVertexRootDensityScale_bounds hc).1
      _ ≤ 2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) := by
            rw [show 2 * (sixVertexAnisotropyMagnitude c /
                (sixVertexAnisotropyMagnitude c - 1)) =
              (2 * sixVertexAnisotropyMagnitude c) /
                (sixVertexAnisotropyMagnitude c - 1) by ring]
            exact (div_le_div_iff_of_pos_right (sub_pos.mpr hd)).2 (by
              linarith)
      _ ≤ 2 * R := by gcongr
  have hK : sixVertexRootDensityKernelUniformBound c ≤ 2 * R ^ 2 := by
    unfold sixVertexRootDensityKernelUniformBound
    calc
      (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) *
          ((sixVertexAnisotropyMagnitude c + 1) /
            sixVertexRootDensityScale c) ≤ R * (2 * R) :=
        mul_le_mul hratio hweight hweight0 (by positivity)
      _ = 2 * R ^ 2 := by ring
  have hK0 := sixVertexRootDensityKernelUniformBound_nonneg hc
  have huniform : sixVertexFiniteRootDensityUniformBound c ≤
      (1 + R) / (2 * Real.pi) := by
    unfold sixVertexFiniteRootDensityUniformBound
    gcongr
  have huniform0 : 0 ≤ sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    positivity
  have hrpi : 0 ≤ (r : Real) / (2 * Real.pi) := by positivity
  have hmeshOne : 0 ≤ (2 * (r : Real) + 1) / lower := by positivity
  have hAWnonneg : 0 ≤ (r : Real) / (2 * Real.pi) *
      ((sixVertexAnisotropyMagnitude c + 1) /
        sixVertexRootDensityScale c) := mul_nonneg hrpi hweight0
  have hA1 : sixVertexRootDensityContractionRate c *
        ((r : Real) / (2 * Real.pi) *
          ((sixVertexAnisotropyMagnitude c + 1) /
            sixVertexRootDensityScale c)) ≤
      (r : Real) / (2 * Real.pi) * (2 * R) := by
    calc
      sixVertexRootDensityContractionRate c *
          ((r : Real) / (2 * Real.pi) *
            ((sixVertexAnisotropyMagnitude c + 1) /
              sixVertexRootDensityScale c)) ≤
        1 * ((r : Real) / (2 * Real.pi) *
          ((sixVertexAnisotropyMagnitude c + 1) /
            sixVertexRootDensityScale c)) := by
              exact mul_le_mul_of_nonneg_right hrate.2.le hAWnonneg
      _ = (r : Real) / (2 * Real.pi) *
          ((sixVertexAnisotropyMagnitude c + 1) /
            sixVertexRootDensityScale c) := by ring
      _ ≤ (r : Real) / (2 * Real.pi) * (2 * R) :=
        mul_le_mul_of_nonneg_left hweight hrpi
  have hA2 : (r : Real) / (2 * Real.pi) *
        sixVertexRootDensityKernelUniformBound c ≤
      (r : Real) / (2 * Real.pi) * (2 * R ^ 2) :=
    mul_le_mul_of_nonneg_left hK hrpi
  have hQ :
      sixVertexRootDensityKernelLipschitzBound c *
            sixVertexFiniteRootDensityUniformBound c *
            ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
          (2 * (r : Real)) * sixVertexRootDensityKernelUniformBound c ≤
        kernelB * ((1 + R) / (2 * Real.pi)) *
            ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
          (2 * (r : Real)) * (2 * R ^ 2) := by
    apply add_le_add
    · gcongr
    · gcongr
  have hQdiv :
      (sixVertexRootDensityKernelLipschitzBound c *
              sixVertexFiniteRootDensityUniformBound c *
              ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
            (2 * (r : Real)) * sixVertexRootDensityKernelUniformBound c) /
          (2 * Real.pi) ≤
        (kernelB * ((1 + R) / (2 * Real.pi)) *
              ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
            (2 * (r : Real)) * (2 * R ^ 2)) /
          (2 * Real.pi) :=
    div_le_div_of_nonneg_right hQ (by positivity)
  unfold sixVertexFixedChargeDensityStabilityErrorOfLower
    sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
  dsimp [B]
  norm_num
  exact add_le_add (add_le_add hA1 hA2) hQdiv

theorem abs_sixVertexFiniteConvolutionDefect_le_fixedCharge_of_lower
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x)
    (x : Real) :
    |sixVertexFiniteConvolutionDefect c N (n + 1) p x| ≤
      sixVertexRootDensityKernelLipschitzBound c *
          sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
            (2 * Real.pi) +
        (2 * (r : Real) / N) * sixVertexRootDensityKernelUniformBound c := by
  have hmesh := sixVertexCyclicRootPartition_mesh_fixedCharge
    hc hN hcharge hopen hsol hlower hdensity
  have hquad :=
    abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge
      hc hN hcharge hopen hsol hmesh
      (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
      (lipschitzWith_sixVertexRootDensityKernel_right hc x)
      (abs_sixVertexRootDensityKernel_le_uniformBound hc x)
  have hsum := sum_cyclicRootPartition_eq_sum_roots_of_periodic p
    (periodic_sixVertexRootDensityKernel_right c x)
  have hsumScaled :
      ∑ k ∈ Finset.range (n + 1),
          (1 / (N : Real)) * sixVertexRootDensityKernel c x
            (sixVertexCyclicRootPartition p k) =
        (∑ j, sixVertexRootDensityKernel c x (p j)) / N := by
    rw [← Finset.mul_sum, hsum]
    ring
  have hint := intervalIntegral_cyclic_kernel_mul_finiteDensity_eq_fullCircle
    (N := N) c p x
  rw [hsumScaled, hint] at hquad
  have hcoe : (sixVertexRootDensityKernelLipschitzNNReal c : Real) =
      sixVertexRootDensityKernelLipschitzBound c := by
    exact Real.coe_toNNReal _
      (sixVertexRootDensityKernelLipschitzBound_pos hc).le
  rw [hcoe] at hquad
  exact hquad

theorem abs_finiteRootDensity_sub_continuumDensity_weighted_le_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {rho : Real → Real} (hrho : Continuous rho)
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {lower E : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
    (hE : 0 ≤ E)
    (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N (n + 1) p y - rho y)| ≤ E)
    (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (n + 1) p x - rho x)| ≤
      sixVertexRootDensityContractionRate c * E +
        sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
  let rhoN := sixVertexFiniteRootDensity c N (n + 1) p
  let e : Real → Real := fun y =>
    sixVertexRootDensityWeight c y * (rhoN y - rho y)
  let D := sixVertexFiniteConvolutionDefect c N (n + 1) p
  let IN : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c z y * rhoN y
  let IR : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c z y * rho y
  let Q := sixVertexRootDensityKernelLipschitzBound c *
      sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
        (2 * Real.pi) +
    (2 * (r : Real) / N) * sixVertexRootDensityKernelUniformBound c
  have hweightCont : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hrhoN : Continuous rhoN :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have he : Continuous e := hweightCont.mul (hrhoN.sub hrho)
  have hrhoNInt : IntervalIntegrable rhoN MeasureTheory.volume
      (-Real.pi) Real.pi := hrhoN.intervalIntegrable _ _
  have hrhoInt : IntervalIntegrable rho MeasureTheory.volume
      (-Real.pi) Real.pi := hrho.intervalIntegrable _ _
  have heMass : ∫ y in -Real.pi..Real.pi,
      e y / sixVertexRootDensityWeight c y = (r : Real) / N := by
    have heq : (fun y => e y / sixVertexRootDensityWeight c y) =
        fun y => rhoN y - rho y := by
      funext y
      dsimp [e]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [heq, intervalIntegral.integral_sub hrhoNInt hrhoInt,
      intervalIntegral_sixVertexFiniteRootDensity hc hN p, hrhoMass]
    have hchargeReal : (N : Real) =
        2 * (n + 1 : Real) + 2 * r := by exact_mod_cast hcharge
    rw [hchargeReal]
    field_simp
    norm_num
    ring
  have hm : 0 ≤ (r : Real) / N := by positivity
  have hcontract := sixVertexRootDensityKernel_contraction_of_fixedMass
    hc he hE hm heMass (by simpa [e, rhoN] using hbound) x
  have hD : |D x| ≤ Q := by
    exact abs_sixVertexFiniteConvolutionDefect_le_fixedCharge_of_lower
      hc hN hcharge hopen hsol hlower hdensity x
  have hkernel : Continuous (sixVertexRootDensityKernel c x) :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have hNInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rhoN y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hrhoN).intervalIntegrable _ _
  have hRInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hrho).intervalIntegrable _ _
  have hJ : (∫ y in -Real.pi..Real.pi,
      (sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y) * e y) = IN x - IR x := by
    rw [show (fun y =>
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
      fun y => sixVertexRootDensityKernel c x y * (rhoN y - rho y) by
        funext y
        dsimp [e]
        field_simp [(sixVertexRootDensityWeight_pos hc y).ne']]
    rw [show (fun y => sixVertexRootDensityKernel c x y * (rhoN y - rho y)) =
      fun y => sixVertexRootDensityKernel c x y * rhoN y -
        sixVertexRootDensityKernel c x y * rho y by funext y; ring]
    exact intervalIntegral.integral_sub hNInt hRInt
  have hNEq : sixVertexRootDensityWeight c x * rhoN x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IN x - (1 / (2 * Real.pi)) * D x := by
    have hfinite := sixVertexRootDensityWeight_mul_finiteRootDensity hc hN p x
    dsimp [rhoN, IN, D, sixVertexFiniteConvolutionDefect]
    rw [hfinite]
    field_simp [Real.pi_ne_zero,
      (by exact_mod_cast hN.ne' : (N : Real) ≠ 0)]
    ring
  have hREq : sixVertexRootDensityWeight c x * rho x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IR x := hrhoEq x hx
  have heqPoint : e x =
      -(1 / (2 * Real.pi)) * (IN x - IR x) -
        (1 / (2 * Real.pi)) * D x := by
    dsimp [e]
    rw [mul_sub, hNEq, hREq]
    ring
  change |e x| ≤ _
  rw [heqPoint, ← hJ]
  calc
    |-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y) -
        (1 / (2 * Real.pi)) * D x| ≤
      |(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y)| +
        |(1 / (2 * Real.pi)) * D x| := by
      simpa [abs_neg] using abs_add_le
        (-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y))
        (-(1 / (2 * Real.pi)) * D x)
    _ ≤ sixVertexRootDensityContractionRate c *
          (E + (((r : Real) / N) / (2 * Real.pi)) *
            ((sixVertexAnisotropyMagnitude c + 1) /
              sixVertexRootDensityScale c)) +
        ((((r : Real) / N) / (2 * Real.pi)) *
          sixVertexRootDensityKernelUniformBound c) +
        Q / (2 * Real.pi) := by
      apply add_le_add hcontract
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
      calc
        (1 / (2 * Real.pi)) * |D x| ≤
            (1 / (2 * Real.pi)) * Q :=
          mul_le_mul_of_nonneg_left hD (by positivity)
        _ = Q / (2 * Real.pi) := by ring
    _ = sixVertexRootDensityContractionRate c * E +
        sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
      unfold sixVertexFixedChargeDensityStabilityErrorOfLower
        sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
      dsimp [Q]
      ring

theorem sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {lower E : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
    (hE : 0 ≤ E)
    (hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤ E) :
    sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤
      sixVertexRootDensityContractionRate c * E +
        sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have herror : 0 ≤
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
    unfold sixVertexFixedChargeDensityStabilityErrorOfLower
      sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
      sixVertexRootDensityKernelUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hs := sixVertexRootDensityScale_pos hc
    have hL := sixVertexRootDensityKernelLipschitzBound_pos hc
    have hK := sixVertexRootDensityKernelUniformBound_nonneg hc
    have hweightUpper : 0 ≤
        (sixVertexAnisotropyMagnitude c + 1) /
          sixVertexRootDensityScale c := by positivity
    have hU : 0 < sixVertexFiniteRootDensityUniformBound c := by
      unfold sixVertexFiniteRootDensityUniformBound
      positivity
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hrN : 0 ≤ (r : Real) / N := div_nonneg (by positivity) hNreal.le
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    have hmassScaled : 0 ≤ ((r : Real) / N) / (2 * Real.pi) := by
      positivity
    have hmeshScaled : 0 ≤
        (2 * (r : Real) + 1) / ((N : Real) * lower) := by positivity
    have hboundaryScaled : 0 ≤ 2 * (r : Real) / N := by positivity
    have hQ : 0 ≤
        sixVertexRootDensityKernelLipschitzBound c *
            sixVertexFiniteRootDensityUniformBound c *
            ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
              (2 * Real.pi) +
          (2 * (r : Real) / N) *
            sixVertexRootDensityKernelUniformBound c := by
      positivity
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hrate.1 (mul_nonneg hmassScaled hweightUpper))
        (mul_nonneg hmassScaled hK))
      (div_nonneg hQ hpi)
  apply sixVertexWeightedFiniteDensityGauge_le_of_pointwise hc p rho
    (add_nonneg (mul_nonneg hrate.1 hE) herror)
  intro x hx
  apply abs_finiteRootDensity_sub_continuumDensity_weighted_le_fixedCharge
    hc hN hcharge hopen hsol rho.continuous hrhoEq hrhoMass hlower
      hdensity hE _ x hx
  intro y hy
  exact (abs_weightedFiniteDensity_sub_le_gauge hc p rho y hy).trans hgauge


theorem sixVertexFiniteRootDensity_lower_half_of_weightedGauge
    {c : Real} (hc : 2 < c) {N n : Nat} {p : Fin n -> Real}
    (rho : C(Real, Real)) {rhoLower outer : Real}
    (hrho : forall x, rhoLower <= rho x)
    (houter : outer <= rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2)
    (hgauge : sixVertexWeightedFiniteDensityGauge hc N n p rho <= outer) :
    forall x, rhoLower / 2 <=
      sixVertexFiniteRootDensity c N n p x := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  intro x
  obtain ⟨y, hy, hxy⟩ :=
    (periodic_sixVertexFiniteRootDensity c N n p).exists_mem_Ioc
      (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
  have hy' : y ∈ Set.Icc (-Real.pi) Real.pi := by
    constructor
    · exact hy.1.le
    · calc
        y <= -Real.pi + 2 * Real.pi := hy.2
        _ = Real.pi := by ring
  have hyclose :=
    (abs_weightedFiniteDensity_sub_le_gauge hc p rho y hy').trans hgauge
  have hdensity := sixVertexFiniteRootDensity_lower_at_of_weighted_close
    hc p (hrho y) hyclose
  change rhoLower - outer / wmin <= _ at hdensity
  have houter' : outer <= rhoLower * wmin / 2 := by
    simpa [wmin] using houter
  have hquot : outer / wmin <= rhoLower / 2 := by
    rw [div_le_iff₀ hwmin]
    nlinarith
  rw [hxy]
  linarith

theorem sixVertexWeightedFiniteDensityGauge_fourier_congr_fixedCharge
    {c1 c2 : Real} (hc1 : 2 < c1) (hc2 : 2 < c2)
    (hc : c1 = c2) {N n : Nat} {p q : Fin n -> Real} (hp : p = q) :
    sixVertexWeightedFiniteDensityGauge hc1 N n p
        (sixVertexFourierPhysicalDensityMap hc1) =
      sixVertexWeightedFiniteDensityGauge hc2 N n q
        (sixVertexFourierPhysicalDensityMap hc2) := by
  subst c2
  subst q
  rfl

theorem sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ x, rhoLower ≤ rho x)
    (houter : outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2)
    (hinner : sixVertexRootDensityContractionRate c * outer +
        sixVertexFixedChargeDensityStabilityErrorOfLower
          c N r (rhoLower / 2) ≤ inner) :
    ¬(inner < sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ∧
      sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho < outer) := by
  rintro ⟨hinnerGauge, hgaugeOuter⟩
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤
      outer := hgaugeOuter.le
  have houterNonneg : 0 ≤ outer :=
    (norm_nonneg (sixVertexWeightedFiniteDensityDifference
      hc N (n + 1) p rho)).trans hgauge
  have hdensity : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c N (n + 1) p x := by
    intro x
    obtain ⟨y, hy, hxy⟩ :=
      (periodic_sixVertexFiniteRootDensity c N (n + 1) p).exists_mem_Ioc
        (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
    have hy' : y ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · exact hy.1.le
      · calc
          y ≤ -Real.pi + 2 * Real.pi := hy.2
          _ = Real.pi := by ring
    have hyclose :=
      (abs_weightedFiniteDensity_sub_le_gauge hc p rho y hy').trans hgauge
    have hx := sixVertexFiniteRootDensity_lower_at_of_weighted_close
      hc p (hrho y) hyclose
    change rhoLower - outer / wmin ≤ _ at hx
    have houter' : outer ≤ rhoLower * wmin / 2 := by
      simpa [wmin] using houter
    have hquot : outer / wmin ≤ rhoLower / 2 := by
      rw [div_le_iff₀ hwmin]
      nlinarith
    rw [hxy]
    linarith
  have himprove := sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge
    hc hN hcharge hopen hsol rho hrhoEq hrhoMass
      (by linarith : 0 < rhoLower / 2) hdensity houterNonneg hgauge
  linarith

theorem sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
    {a b : Real} (ha : 2 < a) {N n q r : Nat} (hN : 0 < N)
    (hq : q = n + 1)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower
            t.1 N r (rhoLower / 2) ≤ inner) :
    ∀ z : SixVertexBetheContinuationSpace a b N q,
      ¬(inner <
          sixVertexContinuationWeightedFiniteDensityGauge ha N q rho z ∧
        sixVertexContinuationWeightedFiniteDensityGauge ha N q rho z <
          outer) := by
  subst q
  intro z
  let t : Set.Icc a b := ⟨z.1.1, z.2.1⟩
  have hc : 2 < z.1.1 := ha.trans_le z.2.1.1
  have htwo : 2 * (n + 1) ≤ N := by omega
  have hopen : SixVertexOpenRootSimplex z.1.2 :=
    sixVertexBetheContinuationSet_subset_open ha htwo z.2
  have hsol : SixVertexSatisfiesBetheEquations
      z.1.1 N (n + 1) z.1.2 :=
    (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
  simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
    sixVertexContinuumDensitySection, t] using
    sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
      hc hN hcharge hopen hsol
      (sixVertexContinuumDensityAt rho t) (hrhoEq t) (hrhoMass t)
      hrhoLower (hrho t) (houter t) (hinner t)

theorem exists_sixVertexContinuousEvenSymmetricBetheBranch_of_fixedChargeDensityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m r : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcharge : N = 2 * (m + m) + 2 * r)
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (hio : inner < outer)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower
            t.1 N r (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
  let k := m + m - 1
  have hk : k + 1 = m + m := by
    dsimp [k]
    omega
  have hrootCount : m + m ≤ N := by omega
  have hcover : 2 * (m + m) ≤ N := by omega
  let g : SixVertexBetheContinuationSpace a b N (m + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
        ha hN (n := k) (q := m + m) (r := r) hk.symm (by omega)
          rho hrhoEq hrhoMass hrhoLower hrho houter hinner
    simpa only [g] using hgap' z
  have hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
      ha hm hN hcover hrootCount rho hrhoLower hrho houter hmargin z hzg
  exact exists_sixVertexContinuousEvenSymmetricBetheBranch_of_stabilityGauge
    ha hab hc₀ hN hcover g hg hio hgap hjac z₀ hz₀g hz₀

theorem exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_fixedChargeDensityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m r : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcharge : N = 2 * (m + m) + 2 * r)
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (hio : inner < outer)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower
            t.1 N r (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexOpenRootSimplex (roots t) ∧
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t)) ∧
      AnalyticOnNhd Real roots (Set.Ioo a b) ∧
      ∀ t (_ht : t ∈ Set.Icc a b),
        ∃ z : SixVertexBetheContinuationSpace a b N (m + m),
          sixVertexContinuationWeightedFiniteDensityGauge
            ha N (m + m) rho z ≤ inner ∧
          z.1.1 = t ∧ z.1.2 = roots t := by
  let k := m + m - 1
  have hk : k + 1 = m + m := by
    dsimp [k]
    omega
  let g : SixVertexBetheContinuationSpace a b N (m + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus_fixedCharge
        ha hN (n := k) (q := m + m) (r := r) hk.symm (by omega)
          rho hrhoEq hrhoMass hrhoLower hrho houter hinner
    simpa only [g] using hgap' z
  have hcover : 2 * (m + m) ≤ N := by omega
  have hcount : m + m ≤ N := by omega
  have hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
      ha hm hN hcover hcount rho hrhoLower hrho houter hmargin z hzg
  exact exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_stabilityGauge
    ha hab hc₀ hN hcover g hg hio hgap hjac z₀ hz₀g hz₀

theorem sixVertexWeightedFiniteDensityGauge_le_fixedChargeAnisotropyError
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * n + 2 * r) (p : Fin n → Real)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    (hrhoNonneg : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, 0 ≤ rho y) :
    sixVertexWeightedFiniteDensityGauge hc N n p rho ≤
      ((1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) +
        (r : Real) / N) / (2 * Real.pi) := by
  let E := 1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hrN : 0 ≤ (r : Real) / N := by positivity
  apply sixVertexWeightedFiniteDensityGauge_le_of_pointwise hc p rho
    (div_nonneg (add_nonneg hE hrN) (by positivity))
  intro x hx
  let K : Real → Real := fun y => sixVertexRootDensityKernel c x y
  let e : Real → Real := fun y => K y - 1
  have hKcont : Continuous K :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have hecont : Continuous e := hKcont.sub continuous_const
  have hrhoInt : IntervalIntegrable rho MeasureTheory.volume
      (-Real.pi) Real.pi := rho.continuous.intervalIntegrable _ _
  have herrInt : IntervalIntegrable (fun y => e y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hecont.mul rho.continuous).intervalIntegrable _ _
  have hErhoInt : IntervalIntegrable (fun y => E * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (continuous_const.mul rho.continuous).intervalIntegrable _ _
  have herrIntegral :
      |∫ y in -Real.pi..Real.pi, e y * rho y| ≤ E / 2 := by
    calc
      |∫ y in -Real.pi..Real.pi, e y * rho y| ≤
          ∫ y in -Real.pi..Real.pi, |e y * rho y| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ y in -Real.pi..Real.pi, E * rho y := by
        apply intervalIntegral.integral_mono_on hab
        · exact (hecont.mul rho.continuous).abs.intervalIntegrable _ _
        · exact hErhoInt
        · intro y hy
          rw [abs_mul, abs_of_nonneg (hrhoNonneg y hy)]
          exact mul_le_mul_of_nonneg_right
            (by simpa only [e, K, E] using
              abs_sixVertexRootDensityKernel_sub_one_le hc x y)
            (hrhoNonneg y hy)
      _ = E / 2 := by
        rw [intervalIntegral.integral_const_mul, hrhoMass]
        ring
  let err : Fin n → Real := fun j => K (p j) - 1
  have herrTerm (j : Fin n) : |err j| ≤ E := by
    simpa only [err, K, E] using
      abs_sixVertexRootDensityKernel_sub_one_le hc x (p j)
  have herrSum : |∑ j, err j| ≤ (n : Real) * E := by
    calc
      |∑ j, err j| ≤ ∑ j, |err j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, E := Finset.sum_le_sum fun j _ => herrTerm j
      _ = (n : Real) * E := by simp
  have hnDensity : (n : Real) / N ≤ 1 / 2 := by
    have hchargeReal : (N : Real) = 2 * n + 2 * r := by
      exact_mod_cast hcharge
    rw [hchargeReal]
    have hden : 0 < 2 * (n : Real) + 2 * r := by
      simpa [hchargeReal] using hNreal
    rw [div_le_iff₀ hden]
    nlinarith
  have herrSumScaled : |(∑ j, err j) / (N : Real)| ≤ E / 2 := by
    rw [abs_div, abs_of_pos hNreal]
    calc
      |∑ j, err j| / (N : Real) ≤ ((n : Real) * E) / N :=
        div_le_div_of_nonneg_right herrSum hNreal.le
      _ = ((n : Real) / N) * E := by ring
      _ ≤ (1 / 2) * E := mul_le_mul_of_nonneg_right hnDensity hE
      _ = E / 2 := by ring
  have hsum : (∑ j, K (p j)) = (n : Real) + ∑ j, err j := by
    calc
      (∑ j, K (p j)) = ∑ j, (1 + err j) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [err, K]
        ring
      _ = (n : Real) + ∑ j, err j := by simp [Finset.sum_add_distrib]
  have hintegral :
      (∫ y in -Real.pi..Real.pi, K y * rho y) =
        1 / 2 + ∫ y in -Real.pi..Real.pi, e y * rho y := by
    rw [show (fun y => K y * rho y) =
        fun y => rho y + e y * rho y by
      funext y
      dsimp [e]
      ring]
    rw [intervalIntegral.integral_add hrhoInt herrInt, hrhoMass]
  have hdiff :
      sixVertexRootDensityWeight c x *
          (sixVertexFiniteRootDensity c N n p x - rho x) =
        ((∫ y in -Real.pi..Real.pi, K y * rho y) -
          (∑ j, K (p j)) / N) / (2 * Real.pi) := by
    rw [mul_sub, sixVertexRootDensityWeight_mul_finiteRootDensity hc hN p x,
      hrhoEq x hx]
    dsimp [K]
    ring
  have hparticleDefect : 1 / 2 - (n : Real) / N = (r : Real) / N := by
    have hchargeReal : (N : Real) = 2 * n + 2 * r := by
      exact_mod_cast hcharge
    field_simp [hNreal.ne']
    linarith
  have hcancel :
      ((∫ y in -Real.pi..Real.pi, K y * rho y) -
          (∑ j, K (p j)) / N) =
        (r : Real) / N +
          (∫ y in -Real.pi..Real.pi, e y * rho y) -
            (∑ j, err j) / N := by
    rw [hintegral, hsum, add_div]
    rw [← hparticleDefect]
    ring
  rw [hdiff, hcancel, abs_div,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * Real.pi)
  calc
    |(r : Real) / N +
        (∫ y in -Real.pi..Real.pi, e y * rho y) -
          (∑ j, err j) / N| ≤
      |(r : Real) / N| +
        |∫ y in -Real.pi..Real.pi, e y * rho y| +
          |(∑ j, err j) / N| := by
      calc
        |_ + _ - _| ≤ |(r : Real) / N +
            (∫ y in -Real.pi..Real.pi, e y * rho y)| +
              |(∑ j, err j) / N| := abs_sub _ _
        _ ≤ (|(r : Real) / N| +
            |∫ y in -Real.pi..Real.pi, e y * rho y|) +
              |(∑ j, err j) / N| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (r : Real) / N + E / 2 + E / 2 := by
      rw [abs_of_nonneg hrN]
      exact add_le_add (add_le_add le_rfl herrIntegral) herrSumScaled
    _ = E + (r : Real) / N := by ring

end
end StatMech.FrontierD
