/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part7


namespace StatMech.Onsager

theorem ons_criticalProductMajorant_inner_intervalIntegrable (x : ℝ) :
    IntervalIntegrable (ons_criticalProductMajorant x)
      MeasureTheory.volume (-Real.pi) Real.pi := by
  unfold ons_criticalProductMajorant
  exact ((ons_criticalOneDimMajorant_intervalIntegrable.const_mul
    (Real.pi * ons_criticalOneDimMajorant x)).add
      intervalIntegral.intervalIntegrable_const).const_mul 32

theorem ons_logGIntBetaDeriv_abs_le_criticalMajorant {b x y : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    |ons_logGIntBetaDeriv b x y| ≤ ons_criticalProductMajorant x y := by
  simpa only [ons_criticalProductMajorant, ons_criticalOneDimMajorant] using
    ons_logGIntBetaDeriv_abs_le_criticalProduct hb hx hy hx0 hy0

theorem ons_criticalDenom_pos_of_left_ne_zero {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    0 < 2 - Real.cos x - Real.cos y :=
  ons_criticalDenom_pos_of_mem_Icc_left hx hx0

theorem ons_gInt_pos_criticalNeighborhood_of_left_ne_zero {b x y : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    0 < ons_gInt b x y := by
  have hA := ons_criticalDenom_pos_of_left_ne_zero (y := y) hx hx0
  have hlower := ons_gInt_lower_criticalNeighborhood (b := b) (k1 := x) (k2 := y) hb
  exact (by positivity : 0 < (Real.sinh (2 * b) - 1) ^ 2 +
    (2 - Real.cos x - Real.cos y) / 4).trans_le hlower

theorem ons_log_gInt_continuous_right_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y => Real.log (ons_gInt b x y)) := by
  have hg : Continuous (fun y => ons_gInt b x y) := by
    unfold ons_gInt
    fun_prop
  exact hg.log fun y =>
    (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hb hx hx0).ne'

theorem ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y => ons_logGIntBetaDeriv b x y) := by
  have hg : Continuous (fun y => ons_gInt b x y) := by
    unfold ons_gInt
    fun_prop
  have hd : Continuous (fun y => ons_gIntBetaDeriv b x y) := by
    unfold ons_gIntBetaDeriv
    fun_prop
  exact hd.div hg fun y =>
    (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hb hx hx0).ne'

theorem ons_ae_ne_zero : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬x ≠ 0} = ({0} : Set ℝ) := by
    ext x
    simp
  rw [hset]
  exact MeasureTheory.measure_singleton 0


theorem ons_hasDerivAt_innerIntegral_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt
      (fun beta => ∫ y in (-Real.pi)..Real.pi,
        Real.log (ons_gInt beta x y))
      (∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv b x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun beta y => Real.log (ons_gInt beta x y))
    (F' := fun beta y => ons_logGIntBetaDeriv beta x y)
    (bound := ons_criticalProductMajorant x) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with beta hbeta
    exact (ons_log_gInt_continuous_right_criticalNeighborhood
      hbeta hx hx0).aestronglyMeasurable
  · exact (ons_log_gInt_continuous_right_criticalNeighborhood hb hx hx0).intervalIntegrable _ _
  · exact (ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood
      hb hx hx0).aestronglyMeasurable
  · filter_upwards [ons_ae_ne_zero] with y hy0 hyI beta hbeta
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      ons_logGIntBetaDeriv_abs_le_criticalMajorant hbeta hx hy hx0 hy0
  · exact ons_criticalProductMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI beta hbeta
    exact ons_hasDerivAt_log_gInt beta x y
      (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hbeta hx hx0).ne'

theorem ons_criticalParameterNeighborhood_sinh_bounds {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    (1 / 2 : ℝ) ≤ Real.sinh (2 * b) ∧ Real.sinh (2 * b) ≤ 2 := by
  refine ⟨hb.1.le, ?_⟩
  have hid := Real.cosh_sq_sub_sinh_sq (2 * b)
  have habsSq := sq_abs (Real.cosh (2 * b))
  have hc := hb.2
  have hcSq : |Real.cosh (2 * b)| ^ 2 < (2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (abs_nonneg _) zero_le_two).2 hc
  have hspos : 0 < Real.sinh (2 * b) := by linarith [hb.1]
  nlinarith

theorem ons_criticalProductMajorant_inner_integral (x : ℝ) :
    (∫ y in (-Real.pi)..Real.pi, ons_criticalProductMajorant x y) =
      32 * (Real.pi * ons_criticalOneDimMajorant x *
        (∫ y in (-Real.pi)..Real.pi, ons_criticalOneDimMajorant y) +
          2 * Real.pi) := by
  have hfirst : IntervalIntegrable
      (fun y => Real.pi * ons_criticalOneDimMajorant x *
        ons_criticalOneDimMajorant y) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    ons_criticalOneDimMajorant_intervalIntegrable.const_mul
      (Real.pi * ons_criticalOneDimMajorant x)
  unfold ons_criticalProductMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hfirst intervalIntegral.intervalIntegrable_const]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  norm_num only [smul_eq_mul]
  ring

end StatMech.Onsager
