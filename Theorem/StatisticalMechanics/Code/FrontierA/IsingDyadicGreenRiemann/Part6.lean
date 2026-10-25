/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Def.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part6
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

theorem isingRegularizedCoordinateGreenComplex_tendsto_zero
    (eta : Real) (heta : 0 < eta) :
    Tendsto (isingRegularizedCoordinateGreenComplex (d := d) eta)
      (cocompact (StrongDual Real (IsingMomentumCoordinates d))) (nhds 0) := by
  have _ := integrable_isingRegularizedCoordinateDensity (d := d) eta heta
  simpa only [isingRegularizedCoordinateGreenComplex] using
    (tendsto_integral_exp_smul_cocompact
      (isingRegularizedCoordinateDensity eta) volume)

theorem isingRegularizedContinuumGreen_eq_re
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    isingRegularizedContinuumGreen eta x =
      (isingRegularizedCoordinateGreenComplex eta
        (isingCoordinateFrequency x)).re := by
  unfold isingRegularizedContinuumGreen
    isingRegularizedCoordinateGreenComplex
  have hDensity := integrable_isingRegularizedCoordinateDensity
    (d := d) eta heta
  have hPhaseContinuous : Continuous
      (fun q : IsingMomentumCoordinates d =>
        (Real.fourierChar (-(isingCoordinateFrequency x) q) : Complex)) := by
    fun_prop
  have hIntegrable : Integrable
      (fun q : IsingMomentumCoordinates d =>
        Real.fourierChar (-(isingCoordinateFrequency x) q) •
          isingRegularizedCoordinateDensity eta q) := by
    rw [show (fun q : IsingMomentumCoordinates d =>
        Real.fourierChar (-(isingCoordinateFrequency x) q) •
          isingRegularizedCoordinateDensity eta q) =
        fun q => (Real.fourierChar
          (-(isingCoordinateFrequency x) q) : Complex) *
            isingRegularizedCoordinateDensity eta q by
      funext q
      rfl]
    apply hDensity.mono
      (hPhaseContinuous.aestronglyMeasurable.mul
        hDensity.aestronglyMeasurable)
    filter_upwards [] with q
    change ‖(Real.fourierChar
        (-(isingCoordinateFrequency x) q) : Complex) *
          isingRegularizedCoordinateDensity eta q‖ ≤ _
    rw [norm_mul, Circle.norm_coe, one_mul]
  calc
    (∫ q in isingNormalizedCoordinateCube d,
        isingRegularizedGreenIntegrand eta x q) =
        ∫ q, (Real.fourierChar
          (-(isingCoordinateFrequency x) q) •
            isingRegularizedCoordinateDensity eta q).re := by
      rw [← integral_indicator
        (measurableSet_isingNormalizedCoordinateCube d)]
      apply integral_congr_ae
      filter_upwards [] with q
      by_cases hq : q ∈ isingNormalizedCoordinateCube d
      · simp only [Set.indicator_of_mem hq]
        rw [isingRegularizedCoordinateDensity,
          Set.indicator_of_mem hq, Circle.smul_def,
          Real.fourierChar_apply, smul_eq_mul, Complex.mul_re]
        simp only [Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
        rw [isingCoordinateFrequency_apply]
        unfold isingRegularizedGreenIntegrand
        rw [show 2 * Real.pi *
            -(∑ i : Fin d, q i * (x i : Real)) =
            -(2 * Real.pi * ∑ i : Fin d, q i * (x i : Real)) by ring,
          Real.cos_neg]
      · simp [Set.indicator_of_notMem hq,
          isingRegularizedCoordinateDensity]
    _ = (∫ q, Real.fourierChar
          (-(isingCoordinateFrequency x) q) •
            isingRegularizedCoordinateDensity eta q).re :=
      integral_re hIntegrable

theorem isingCoordinateFrequency_coord_abs_le_norm
    (x : Fin d → Int) (i : Fin d) :
    |(x i : Real)| ≤ ‖isingCoordinateFrequency x‖ := by
  let e : IsingMomentumCoordinates d := Pi.single i 1
  have heNorm : ‖e‖ = 1 := by
    change ‖(Pi.single i 1 : Fin d → Real)‖ = 1
    rw [Pi.norm_single]
    norm_num
  have happ : isingCoordinateFrequency x e = (x i : Real) := by
    rw [isingCoordinateFrequency_apply]
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j _ hji
      simp [e, hji]
    · simp
  calc
    |(x i : Real)| = ‖isingCoordinateFrequency x e‖ := by
      rw [happ, Real.norm_eq_abs]
    _ ≤ ‖isingCoordinateFrequency x‖ * ‖e‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖isingCoordinateFrequency x‖ := by rw [heNorm, mul_one]


theorem isingRegularizedContinuumGreen_decay
    (eta : Real) (heta : 0 < eta) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Nat, ∀ x : Site d, x ∉ box d R →
      |isingRegularizedContinuumGreen eta x| < epsilon := by
  have htend := isingRegularizedCoordinateGreenComplex_tendsto_zero
    (d := d) eta heta
  have hevent : ∀ᶠ w : StrongDual Real (IsingMomentumCoordinates d) in
      cocompact (StrongDual Real (IsingMomentumCoordinates d)),
      ‖isingRegularizedCoordinateGreenComplex eta w‖ < epsilon := by
    have hmetric := (Metric.tendsto_nhds.mp htend) epsilon hepsilon
    filter_upwards [hmetric] with w hw
    simpa only [dist_zero_right] using hw
  obtain ⟨K, hKcompact, hKsub⟩ := Filter.mem_cocompact.mp hevent
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hKcompact.isBounded
  obtain ⟨R, hR⟩ := exists_nat_gt C
  refine ⟨R, ?_⟩
  intro x hx
  have hxExists : ∃ i : Fin d, R < (x i).natAbs := by
    simpa only [mem_box, not_forall, not_le] using hx
  obtain ⟨i, hi⟩ := hxExists
  have habs : (R : Real) < |(x i : Real)| := by
    have hiInt : (R : Int) < |x i| := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hi
    exact_mod_cast hiInt
  have hfreqNotMem : isingCoordinateFrequency x ∉ K := by
    intro hmem
    have hnorm := hC _ hmem
    have hcoord := isingCoordinateFrequency_coord_abs_le_norm x i
    linarith
  have hcomplex :
      ‖isingRegularizedCoordinateGreenComplex eta
        (isingCoordinateFrequency x)‖ < epsilon :=
    hKsub (by simpa using hfreqNotMem)
  rw [isingRegularizedContinuumGreen_eq_re eta heta x]
  exact (Complex.abs_re_le_norm _).trans_lt hcomplex


theorem isingRegularizedGridGreen_tendsto
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Tendsto (isingRegularizedGridGreen eta x) atTop
      (nhds (isingRegularizedContinuumGreen eta x)) := by
  simpa only [isingRegularizedGridGreen, isingRegularizedContinuumGreen,
    isingUnitMomentumLattice, Fintype.card_fin] using
    (tendsto_tsum_div_pow_atTop_integral
      (isingNormalizedCoordinateCube d)
      (isingRegularizedGreenIntegrand eta x)
      (continuous_isingRegularizedGreenIntegrand eta heta x)
      (isBounded_isingNormalizedCoordinateCube d)
      (measurableSet_isingNormalizedCoordinateCube d)
      (volume_frontier_isingNormalizedCoordinateCube d))


theorem isingRegularizedDyadicGridGreen_tendsto
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Tendsto (fun k =>
      isingRegularizedGridGreen eta x (isingDyadicSide k)) atTop
      (nhds (isingRegularizedContinuumGreen eta x)) := by
  have hside : Tendsto isingDyadicSide atTop atTop := by
    unfold isingDyadicSide
    rw [Filter.tendsto_add_atTop_iff_nat]
    exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
  exact (isingRegularizedGridGreen_tendsto eta heta x).comp
    hside


theorem isingRegularizedTorusGreen_tendsto
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Tendsto (isingRegularizedTorusGreen eta x) atTop
      (nhds (isingRegularizedContinuumGreen eta x)) := by
  rw [show isingRegularizedTorusGreen eta x =
      fun k => isingRegularizedGridGreen eta x (isingDyadicSide k) by
    funext k
    exact isingRegularizedTorusGreen_eq_grid eta x k]
  exact isingRegularizedDyadicGridGreen_tendsto eta heta x


theorem isingDyadicTorusGreen_eventually_close_continuum
    (hd : 2 < d) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ eta : Real, 0 < eta ∧ ∀ x : Site d,
      ∀ᶠ k : Nat in atTop,
        |isingDyadicTorusGreen x k -
          isingRegularizedContinuumGreen eta x| < epsilon := by
  obtain ⟨C, hCpos, hC⟩ :=
    isingTorusLowMomentum_inverseDispersion_le hd
  let delta : Real := min (1 / 4) (epsilon / (16 * C))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (div_pos hepsilon (mul_pos (by norm_num) hCpos))
  have hdeltaQuarter : delta ≤ 1 / 4 := min_le_left _ _
  have hdeltaHalf : delta ≤ 1 / 2 := hdeltaQuarter.trans (by norm_num)
  have hdeltaEps : delta ≤ epsilon / (16 * C) := min_le_right _ _
  let eta : Real := 16 * delta ^ 2
  have heta : 0 < eta := by dsimp [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro x
  have hsideNat : Tendsto isingDyadicSide atTop atTop := by
    unfold isingDyadicSide
    rw [Filter.tendsto_add_atTop_iff_nat]
    exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
  have hsideReal : Tendsto (fun k => (isingDyadicSide k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hsideNat
  have hlargeDelta : ∀ᶠ k : Nat in atTop,
      1 / delta ≤ (isingDyadicSide k : Real) :=
    hsideReal.eventually_ge_atTop (1 / delta)
  have hlargeZero : ∀ᶠ k : Nat in atTop,
      8 * eta⁻¹ / epsilon ≤ (isingDyadicSide k : Real) :=
    hsideReal.eventually_ge_atTop (8 * eta⁻¹ / epsilon)
  have hreg := isingRegularizedTorusGreen_tendsto eta heta x
  have hregClose : ∀ᶠ k : Nat in atTop,
      |isingRegularizedTorusGreen eta x k -
        isingRegularizedContinuumGreen eta x| < epsilon / 2 := by
    have hmetric := (Metric.tendsto_nhds.mp hreg)
      (epsilon / 2) (half_pos hepsilon)
    filter_upwards [hmetric] with k hk
    simpa only [Real.dist_eq] using hk
  filter_upwards [hlargeDelta, hlargeZero, hregClose] with k hkDelta hkZero hkReg
  let M : Nat := ⌈delta * isingDyadicSide k⌉₊
  have hMpos : 1 ≤ M := by
    dsimp [M]
    have hsReal : (0 : Real) < (isingDyadicSide k : Real) := by
      exact_mod_cast isingDyadicSide_pos k
    have hpos := Nat.ceil_pos.mpr (mul_pos hdelta hsReal)
    exact hpos
  have hMhalf : M ≤ isingDyadicSide k / 2 := by
    exact isingLowMomentumRadius_le_half delta hdelta.le hdeltaHalf
  have hsupport : ∀ p : IsingDyadicTorus d k, p ≠ 0 →
      isingTorusCharacterDispersion (isingTorusMomentumChar p) < eta →
      p ∈ isingTorusLowMomentum d k M := by
    intro p hp0 hpeta
    exact isingTorus_smallDispersion_mem_lowMomentum
      delta eta hdelta hdeltaHalf (le_refl eta) p hp0 hpeta
  have hfinite := isingDyadicTorusGreen_sub_regularized_abs_le
    eta heta x hsupport
  have hLpos : (0 : Real) < isingDyadicSide k := by
    exact_mod_cast isingDyadicSide_pos k
  have hLone : (1 : Real) ≤ isingDyadicSide k := by
    exact_mod_cast (show 1 ≤ isingDyadicSide k by
      exact Nat.one_le_iff_ne_zero.mpr (isingDyadicSide_pos k).ne')
  have hdOne : 1 ≤ d := by omega
  have hLpow : (isingDyadicSide k : Real) ≤
      (isingDyadicSide k : Real) ^ d := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hLone hdOne :
        (isingDyadicSide k : Real) ^ 1 ≤
          (isingDyadicSide k : Real) ^ d)
  have hzero :
      (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ ≤ epsilon / 8 := by
    have hetaInv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
    have hfirst :
        (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ ≤
          eta⁻¹ / (isingDyadicSide k : Real) := by
      rw [one_div, div_eq_mul_inv, mul_comm eta⁻¹]
      gcongr
    calc
      (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ ≤
          eta⁻¹ / (isingDyadicSide k : Real) := hfirst
      _ ≤ epsilon / 8 := by
        apply (div_le_iff₀ hLpos).2
        have hprod := mul_le_mul_of_nonneg_left hkZero hepsilon.le
        have hetaInvPos : 0 < eta⁻¹ := inv_pos.mpr heta
        field_simp [hepsilon.ne', heta.ne'] at hprod ⊢
        nlinarith
  have hMratio : (M : Real) / isingDyadicSide k < 2 * delta := by
    have hceil := Nat.ceil_lt_add_one
      (mul_nonneg hdelta.le (by positivity) :
        0 ≤ delta * (isingDyadicSide k : Real))
    have hceilM : (M : Real) <
        delta * (isingDyadicSide k : Real) + 1 := by
      simpa only [M] using hceil
    apply (div_lt_iff₀ hLpos).2
    have hinvBound : 1 ≤ delta * (isingDyadicSide k : Real) := by
      calc
        1 = delta * (1 / delta) := by field_simp
        _ ≤ delta * (isingDyadicSide k : Real) :=
          mul_le_mul_of_nonneg_left hkDelta hdelta.le
    nlinarith [hceilM]
  have hbase : 0 ≤ (M : Real) / isingDyadicSide k := by positivity
  have hlowRaw := hC k M hMpos hMhalf
  have hlow :
      (1 / (isingDyadicSide k : Real) ^ d) *
          ∑ p ∈ isingTorusLowMomentum d k M,
            (isingTorusCharacterDispersion
              (isingTorusMomentumChar p))⁻¹ ≤ epsilon / 8 := by
    have htwoDelta : 0 ≤ 2 * delta := by positivity
    have hpowMono :
        ((M : Real) / isingDyadicSide k) ^ (d - 2) ≤
          (2 * delta) ^ (d - 2) :=
      pow_le_pow_left₀ hbase hMratio.le _
    have htwoLeOne : 2 * delta ≤ 1 := by linarith
    have hexp : 1 ≤ d - 2 := by omega
    have hpowSmall : (2 * delta) ^ (d - 2) ≤ 2 * delta := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one htwoDelta htwoLeOne hexp :
          (2 * delta) ^ (d - 2) ≤ (2 * delta) ^ 1)
    calc
      (1 / (isingDyadicSide k : Real) ^ d) *
          ∑ p ∈ isingTorusLowMomentum d k M,
            (isingTorusCharacterDispersion
              (isingTorusMomentumChar p))⁻¹ ≤
          C * ((M : Real) / isingDyadicSide k) ^ (d - 2) := hlowRaw
      _ ≤ C * (2 * delta) ^ (d - 2) := by gcongr
      _ ≤ C * (2 * delta) := by gcongr
      _ ≤ epsilon / 8 := by
        have hmul := mul_le_mul_of_nonneg_left hdeltaEps hCpos.le
        field_simp [hCpos.ne'] at hmul ⊢
        nlinarith
  have hfiniteSmall : |isingDyadicTorusGreen x k -
      isingRegularizedTorusGreen eta x k| ≤ epsilon / 4 := by
    calc
      |isingDyadicTorusGreen x k - isingRegularizedTorusGreen eta x k| ≤
          (1 / (isingDyadicSide k : Real) ^ d) *
            (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
              (isingTorusCharacterDispersion
                (isingTorusMomentumChar p))⁻¹) := hfinite
      _ = (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ +
          (1 / (isingDyadicSide k : Real) ^ d) *
            ∑ p ∈ isingTorusLowMomentum d k M,
              (isingTorusCharacterDispersion
                (isingTorusMomentumChar p))⁻¹ := by ring
      _ ≤ epsilon / 8 + epsilon / 8 := add_le_add hzero hlow
      _ = epsilon / 4 := by ring
  calc
    |isingDyadicTorusGreen x k - isingRegularizedContinuumGreen eta x| ≤
        |isingDyadicTorusGreen x k - isingRegularizedTorusGreen eta x k| +
          |isingRegularizedTorusGreen eta x k -
            isingRegularizedContinuumGreen eta x| := by
      simpa only [sub_add_sub_cancel] using
        (abs_add_le
          (isingDyadicTorusGreen x k - isingRegularizedTorusGreen eta x k)
          (isingRegularizedTorusGreen eta x k -
            isingRegularizedContinuumGreen eta x))
    _ < epsilon / 4 + epsilon / 2 := add_lt_add_of_le_of_lt hfiniteSmall hkReg
    _ < epsilon := by linarith


theorem isingDyadicTorusGreen_eventually_small_outside_box
    (hd : 2 < d) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Nat, ∀ x : Site d, x ∉ box d R →
      ∀ᶠ k : Nat in atTop, |isingDyadicTorusGreen x k| < epsilon := by
  obtain ⟨eta, heta, hclose⟩ :=
    isingDyadicTorusGreen_eventually_close_continuum
      hd (epsilon / 2) (half_pos hepsilon)
  obtain ⟨R, hR⟩ := isingRegularizedContinuumGreen_decay
    eta heta (epsilon / 2) (half_pos hepsilon)
  refine ⟨R, ?_⟩
  intro x hx
  have hlimit := hR x hx
  filter_upwards [hclose x] with k hk
  calc
    |isingDyadicTorusGreen x k| =
        |(isingDyadicTorusGreen x k -
            isingRegularizedContinuumGreen eta x) +
          isingRegularizedContinuumGreen eta x| := by ring_nf
    _ ≤ |isingDyadicTorusGreen x k -
          isingRegularizedContinuumGreen eta x| +
        |isingRegularizedContinuumGreen eta x| := abs_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hk hlimit
    _ = epsilon := by ring

end StatMech.FrontierA
