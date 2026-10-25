/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part8


namespace StatMech.Onsager

theorem ons_criticalOuterMajorant_intervalIntegrable :
    IntervalIntegrable ons_criticalOuterMajorant MeasureTheory.volume
      (-Real.pi) Real.pi := by
  let J : ℝ := ∫ y in (-Real.pi)..Real.pi, ons_criticalOneDimMajorant y
  have hterm : IntervalIntegrable
      (fun x => Real.pi * ons_criticalOneDimMajorant x * J)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    convert ons_criticalOneDimMajorant_intervalIntegrable.const_mul (Real.pi * J) using 1
    ext x
    ring
  unfold ons_criticalOuterMajorant
  change IntervalIntegrable
    (fun x => 32 * (Real.pi * ons_criticalOneDimMajorant x * J + 2 * Real.pi))
    MeasureTheory.volume (-Real.pi) Real.pi
  exact (hterm.add intervalIntegral.intervalIntegrable_const).const_mul 32

theorem ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ‖∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y‖ ≤
      ons_criticalOuterMajorant x := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun y => ons_logGIntBetaDeriv b x y)
    (g := ons_criticalProductMajorant x)
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) (by
      filter_upwards [ons_ae_ne_zero] with y hy0 hyI
      have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
        exact ⟨hyI.1.le, hyI.2⟩
      simpa only [Real.norm_eq_abs] using
        ons_logGIntBetaDeriv_abs_le_criticalMajorant hb hx hy hx0 hy0)
    (ons_criticalProductMajorant_inner_intervalIntegrable x)
  rw [ons_criticalProductMajorant_inner_integral] at hnorm
  exact hnorm


theorem ons_hasDerivAt_doubleIntegral_betaC :
    HasDerivAt
      (fun b => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi, Real.log (ons_gInt b x y))
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv ons_betaC x y) ons_betaC := by
  have hself : ons_betaC ∈ ons_criticalParameterNeighborhood :=
    mem_of_mem_nhds ons_criticalParameterNeighborhood_mem_nhds
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (ons_gInt b x y))
    (F' := fun b x => ∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv b x y)
    (bound := ons_criticalOuterMajorant)
    ons_criticalParameterNeighborhood_mem_nhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [ons_criticalParameterNeighborhood_mem_nhds] with b hb
    have hs := ons_criticalParameterNeighborhood_sinh_bounds hb
    exact (ons_inner_integral_continuous_near_betaC b hs.1 hs.2).aestronglyMeasurable
  · exact (ons_inner_integral_continuous_near_betaC ons_betaC
      (by rw [ons_betaC_sinh]; norm_num)
      (by rw [ons_betaC_sinh]; norm_num)).intervalIntegrable _ _
  · apply (continuous_const.aestronglyMeasurable :
      MeasureTheory.AEStronglyMeasurable
        (fun _x : ℝ => (2 * Real.pi) * (2 * Real.cosh (2 * ons_betaC)))
        (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi))).congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
    have hx' := Set.uIoc_subset_uIcc hx
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx'
    exact (ons_criticalFirst_inner_integral x hx').symm
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI b hb
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant hb hx hx0
  · exact ons_criticalOuterMajorant_intervalIntegrable
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI b hb
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_hasDerivAt_innerIntegral_criticalNeighborhood hb hx hx0

theorem ons_hasDerivAt_freeEnergyIntegral_betaC :
    HasDerivAt ons_freeEnergyIntegral (Real.sqrt 2) ons_betaC := by
  have h := ons_hasDerivAt_doubleIntegral_betaC.const_mul
    (1 / (8 * Real.pi ^ 2))
  unfold ons_freeEnergyIntegral
  convert h using 1
  exact ons_criticalFirst_normalized_integral_eq_sqrt_two.symm

theorem ons_hasDerivAt_pressure_betaC :
    HasDerivAt ons_pressure (Real.sqrt 2) ons_betaC := by
  change HasDerivAt (fun b => Real.log 2 + ons_freeEnergyIntegral b)
    (Real.sqrt 2) ons_betaC
  simpa only [Pi.add_apply, zero_add] using
    (hasDerivAt_const ons_betaC (Real.log 2)).add
      ons_hasDerivAt_freeEnergyIntegral_betaC

theorem ons_innerLogDerivIntegral_aestronglyMeasurable (b : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv b x y)
      (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ons_logGIntBetaDeriv b p.1 p.2) (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    unfold ons_logGIntBetaDeriv ons_gIntBetaDeriv ons_gInt
    fun_prop
  have hi := hjoint.integral_prod_right'
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simpa only [μ, intervalIntegral.integral_of_le hpi,
    Set.uIoc_of_le hpi] using hi

theorem ons_innerLogDerivIntegral_continuousAt_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ContinuousAt
      (fun beta => ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv beta x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (ons_criticalProductMajorant x)
  · filter_upwards [hs] with beta hbeta
    exact (ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood
      hbeta hx hx0).aestronglyMeasurable
  · filter_upwards [hs] with beta hbeta
    filter_upwards [ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      ons_logGIntBetaDeriv_abs_le_criticalMajorant hbeta hx hy hx0 hy0
  · exact ons_criticalProductMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI
    exact (ons_hasDerivAt_logGIntBetaDeriv b x y
      (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hb hx hx0).ne').continuousAt

theorem ons_firstDerivativeDoubleIntegral_continuousAt_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    ContinuousAt
      (fun beta => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv beta x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    ons_criticalOuterMajorant
  · exact Filter.Eventually.of_forall ons_innerLogDerivIntegral_aestronglyMeasurable
  · filter_upwards [hs] with beta hbeta
    filter_upwards [ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant hbeta hx hx0
  · exact ons_criticalOuterMajorant_intervalIntegrable
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_continuousAt_criticalNeighborhood hb hx hx0

theorem ons_firstDerivativeDoubleIntegral_continuousOn_criticalNeighborhood :
    ContinuousOn
      (fun beta => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv beta x y)
      ons_criticalParameterNeighborhood := by
  intro b hb
  exact (ons_firstDerivativeDoubleIntegral_continuousAt_criticalNeighborhood hb).continuousWithinAt

theorem ons_hasDerivAt_doubleIntegral_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    HasDerivAt
      (fun beta => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi, Real.log (ons_gInt beta x y))
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv b x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  have hsinh := ons_criticalParameterNeighborhood_sinh_bounds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun beta x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (ons_gInt beta x y))
    (F' := fun beta x => ∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv beta x y)
    (bound := ons_criticalOuterMajorant) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with beta hbeta
    have hsbeta := ons_criticalParameterNeighborhood_sinh_bounds hbeta
    exact (ons_inner_integral_continuous_near_betaC beta
      hsbeta.1 hsbeta.2).aestronglyMeasurable
  · exact (ons_inner_integral_continuous_near_betaC b
      hsinh.1 hsinh.2).intervalIntegrable _ _
  · exact ons_innerLogDerivIntegral_aestronglyMeasurable b
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI beta hbeta
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant hbeta hx hx0
  · exact ons_criticalOuterMajorant_intervalIntegrable
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI beta hbeta
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_hasDerivAt_innerIntegral_criticalNeighborhood hbeta hx hx0

theorem ons_hasDerivAt_freeEnergyIntegral_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    HasDerivAt ons_freeEnergyIntegral
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ x in (-Real.pi)..Real.pi,
          ∫ y in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv b x y) b := by
  unfold ons_freeEnergyIntegral
  exact (ons_hasDerivAt_doubleIntegral_criticalNeighborhood hb).const_mul
    (1 / (8 * Real.pi ^ 2))

theorem ons_hasDerivAt_pressure_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    HasDerivAt ons_pressure
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ x in (-Real.pi)..Real.pi,
          ∫ y in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv b x y) b := by
  change HasDerivAt (fun beta => Real.log 2 + ons_freeEnergyIntegral beta) _ b
  simpa only [Pi.add_apply, zero_add] using
    (hasDerivAt_const b (Real.log 2)).add
      (ons_hasDerivAt_freeEnergyIntegral_criticalNeighborhood hb)


theorem ons_pressure_contDiffAt_one_betaC :
    ContDiffAt ℝ 1 ons_pressure ons_betaC := by
  let d : ℝ → ℝ := fun b =>
    (1 / (8 * Real.pi ^ 2)) *
      ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv b x y
  let f' : ℝ → ℝ →L[ℝ] ℝ := fun b =>
    d b • ContinuousLinearMap.id ℝ ℝ
  rw [contDiffAt_one_iff]
  refine ⟨f', ons_criticalParameterNeighborhood,
    ons_criticalParameterNeighborhood_mem_nhds, ?_, ?_⟩
  · have hd : ContinuousOn d ons_criticalParameterNeighborhood := by
      exact ons_firstDerivativeDoubleIntegral_continuousOn_criticalNeighborhood.const_mul
        (1 / (8 * Real.pi ^ 2))
    exact hd.smul continuousOn_const
  · intro b hb
    rw [hasFDerivAt_iff_hasDerivAt]
    simpa only [f', d, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using
      ons_hasDerivAt_pressure_criticalNeighborhood hb


end StatMech.Onsager
