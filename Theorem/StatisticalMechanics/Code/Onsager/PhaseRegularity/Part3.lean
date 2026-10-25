/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part3


namespace StatMech.Onsager

theorem ons_criticalSecondKernelClamp_continuous (epsilon : ℝ)
    (hcut : 0 < 1 - Real.cos epsilon) :
    Continuous (Function.uncurry (ons_criticalSecondKernelClamp epsilon)) := by
  have hk := ons_criticalKernelClamp_continuous epsilon hcut
  exact continuous_const.add (continuous_const.mul hk)

theorem ons_criticalSecondKernel_inner_continuousOn {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  have hclamp := ons_wedgeIntegral_continuous
    (ons_criticalSecondKernelClamp_continuous epsilon hcut)
  apply hclamp.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  rw [ons_criticalSecondKernelClamp,
    ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx,
    ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos
      (hepsilon.trans_le hx.1) hxPi).ne']
  ring

theorem ons_criticalSecondComparison_integral {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) :
    (∫ x in epsilon..1, (-4 + 32 / (5 * x))) =
      -4 * (1 - epsilon) + (32 / 5 : ℝ) * Real.log (1 / epsilon) := by
  have hconst : IntervalIntegrable (fun _x : ℝ => (-4 : ℝ))
      MeasureTheory.volume epsilon 1 := continuousOn_const.intervalIntegrable
  have hlog : IntervalIntegrable (fun x : ℝ => 32 / (5 * x))
      MeasureTheory.volume epsilon 1 := by
    have hcont : ContinuousOn (fun x : ℝ => 32 / (5 * x))
        (Set.uIcc epsilon 1) := by
      apply ContinuousOn.div continuousOn_const
        (continuousOn_const.mul continuousOn_id)
      intro x hx hzero
      change 5 * x = 0 at hzero
      rw [Set.mem_uIcc] at hx
      rcases hx with hx | hx <;> nlinarith
    exact hcont.intervalIntegrable
  rw [intervalIntegral.integral_add hconst hlog, intervalIntegral.integral_const]
  norm_num only [smul_eq_mul]
  have hscale : (∫ x in epsilon..1, 32 / (5 * x)) =
      16 * ∫ x in epsilon..1, 2 / (5 * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hscale, ons_logKernel_integral hepsilon hepsilonOne]
  ring

theorem ons_criticalSecond_wedgeCutoff_lower (n : ℕ) :
    -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..1,
        ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  change -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonOne : epsilon ≤ 1 := by
    change Real.exp (-(n : ℝ)) ≤ 1
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have hdeltaPi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hinnerInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecondKernel_inner_continuousOn hepsilon hepsilonOne hdeltaPi
  have hcompCont : ContinuousOn (fun x : ℝ => -4 + 32 / (5 * x))
      (Set.uIcc epsilon 1) := by
    apply continuousOn_const.add
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.mul continuousOn_id)
    intro x hx hzero
    change 5 * x = 0 at hzero
    rw [Set.mem_uIcc] at hx
    rcases hx with hx | hx <;> nlinarith
  have hcompInt : IntervalIntegrable (fun x : ℝ => -4 + 32 / (5 * x))
      MeasureTheory.volume epsilon 1 := hcompCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hepsilonOne hcompInt hinnerInt
    (fun x hx => by
      rcases hx with ⟨hxlo, hxhi⟩
      have hinner := ons_criticalSecondKernel_innerIntegral_lower
        (hepsilon.trans_le hxlo) (by linarith [hxhi, Real.pi_gt_three])
      nlinarith)
  rw [ons_criticalSecondComparison_integral hepsilon hepsilonOne] at hmono
  have hlog : Real.log (1 / epsilon) = (n : ℝ) := by
    rw [show epsilon = Real.exp (-(n : ℝ)) by rfl,
      Real.log_div one_ne_zero (Real.exp_ne_zero _), Real.log_one,
      Real.log_exp]
    ring
  rw [hlog] at hmono
  nlinarith


theorem ons_criticalSecond_wedgeCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..1,
          ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono ons_criticalSecond_wedgeCutoff_lower
  have hbase : Filter.Tendsto (fun n : ℕ => (32 / 5 : ℝ) * (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  exact tendsto_const_nhds.add_atTop hbase

theorem ons_criticalSecondKernel_ge_neg_four {x y : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    -4 ≤ ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hdenPos := ons_criticalDenom_pos (y := y) hx hxpi
  rw [ons_logGIntBetaDeriv2_betaC x y hdenPos.ne']
  have hnonneg : 0 ≤ 16 / (2 - Real.cos x - Real.cos y) :=
    div_nonneg (by norm_num) hdenPos.le
  linarith

theorem ons_criticalSecondKernel_intervalIntegrable {x a b : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    IntervalIntegrable (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume a b := by
  have hdenCont : Continuous (fun y : ℝ => 2 - Real.cos x - Real.cos y) :=
    (show Continuous (fun y : ℝ => (2 - Real.cos x) - Real.cos y) from
      continuous_const.sub Real.continuous_cos)
  have hkernelCont : Continuous
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y)) := by
    apply Continuous.div continuous_const hdenCont
    intro y
    exact (ons_criticalDenom_pos hx hxpi).ne'
  have hexpr : Continuous
      (fun y : ℝ => -4 + 16 * (1 / (2 - Real.cos x - Real.cos y))) :=
    continuous_const.add (continuous_const.mul hkernelCont)
  have hsecond : Continuous
      (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y) := by
    apply hexpr.congr
    intro y
    change -4 + 16 * (1 / (2 - Real.cos x - Real.cos y)) =
      ons_logGIntBetaDeriv2 ons_betaC x y
    rw [ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos hx hxpi).ne']
    ring
  exact hsecond.continuousOn.intervalIntegrable

theorem ons_criticalSecondKernel_interval_lower {x a b : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) (hab : a ≤ b) :
    -4 * (b - a) ≤
      ∫ y in a..b, ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hconst : IntervalIntegrable (fun _y : ℝ => (-4 : ℝ))
      MeasureTheory.volume a b := continuousOn_const.intervalIntegrable
  have hsecond := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := a) (b := b)
  have hmono := intervalIntegral.integral_mono_on hab hconst hsecond
    (fun y _hy => ons_criticalSecondKernel_ge_neg_four hx hxpi)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  simpa [mul_comm] using hmono


theorem ons_criticalSecondKernel_rectInner_lower {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) :
    (∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) - 8 ≤
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hxpi : x ≤ Real.pi := hxone.trans (by linarith [Real.pi_gt_three])
  have h0x := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := 0) (b := x)
  have hxx2 := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := x) (b := 2 * x)
  have hx22 := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := 2 * x) (b := 2)
  have hlower0 := ons_criticalSecondKernel_interval_lower hx hxpi (show 0 ≤ x from hx.le)
  have hlower2 := ons_criticalSecondKernel_interval_lower hx hxpi
    (show 2 * x ≤ 2 by linarith)
  have hjoin1 := intervalIntegral.integral_add_adjacent_intervals h0x hxx2
  have hjoin2 := intervalIntegral.integral_add_adjacent_intervals
    (h0x.trans hxx2) hx22
  linarith

theorem ons_criticalSecond_rectInner_continuousOn {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  have hjoint := ons_criticalSecondKernelClamp_continuous epsilon hcut
  have hclamp : Continuous (fun x : ℝ =>
      ∫ y in 0..2, ons_criticalSecondKernelClamp epsilon x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hjoint 0 2
  apply hclamp.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  rw [ons_criticalSecondKernelClamp,
    ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx,
    ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos
      (hepsilon.trans_le hx.1) hxPi).ne']
  ring

theorem ons_criticalSecond_fixedInner_continuousOn {epsilon delta a b : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in a..b, ons_logGIntBetaDeriv2 ons_betaC x y)
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  have hjoint := ons_criticalSecondKernelClamp_continuous epsilon hcut
  have hclamp : Continuous (fun x : ℝ =>
      ∫ y in a..b, ons_criticalSecondKernelClamp epsilon x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hjoint a b
  apply hclamp.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  rw [ons_criticalSecondKernelClamp,
    ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx,
    ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos
      (hepsilon.trans_le hx.1) hxPi).ne']
  ring

theorem ons_criticalSecond_rectCutoff_lower (n : ℕ) :
    -12 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..1,
        ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  change -12 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonOne : epsilon ≤ 1 := by
    change Real.exp (-(n : ℝ)) ≤ 1
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hwedgeInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecondKernel_inner_continuousOn hepsilon hepsilonOne hpi
  have hleftInt : IntervalIntegrable (fun x : ℝ =>
      (∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) - 8)
      MeasureTheory.volume epsilon 1 :=
    hwedgeInt.sub (continuousOn_const.intervalIntegrable)
  have hrectInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecond_rectInner_continuousOn hepsilon hepsilonOne hpi
  have hmono := intervalIntegral.integral_mono_on hepsilonOne hleftInt hrectInt
    (fun x hx => ons_criticalSecondKernel_rectInner_lower
      (hepsilon.trans_le hx.1) hx.2)
  rw [intervalIntegral.integral_sub hwedgeInt
    (continuousOn_const.intervalIntegrable), intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  have hwedge := ons_criticalSecond_wedgeCutoff_lower n
  change -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y at hwedge
  nlinarith


theorem ons_criticalSecond_rectCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..1,
          ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono ons_criticalSecond_rectCutoff_lower
  have hbase : Filter.Tendsto (fun n : ℕ => (32 / 5 : ℝ) * (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  exact tendsto_const_nhds.add_atTop hbase

theorem ons_criticalSecond_positiveInner_rect_lower {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) :
    (∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) - 4 * Real.pi ≤
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hxpi : x ≤ Real.pi := hxone.trans (by linarith [Real.pi_gt_three])
  have h02 := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := 0) (b := 2)
  have h2pi := ons_criticalSecondKernel_intervalIntegrable hx hxpi
    (a := 2) (b := Real.pi)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals h02 h2pi
  have hlower := ons_criticalSecondKernel_interval_lower hx hxpi
    (show (2 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
  linarith [Real.pi_pos]

theorem ons_criticalSecond_positiveQuadrantCutoff_lower (n : ℕ) :
    -12 - 4 * Real.pi ^ 2 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..Real.pi,
        ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  change -12 - 4 * Real.pi ^ 2 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..Real.pi,
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonOne : epsilon ≤ 1 := by
    change Real.exp (-(n : ℝ)) ≤ 1
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have honePi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hrectInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecond_rectInner_continuousOn hepsilon hepsilonOne honePi
  have hpositiveInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecond_fixedInner_continuousOn
        (a := 0) (b := Real.pi) hepsilon hepsilonOne honePi
  have hleftInt : IntervalIntegrable (fun x : ℝ =>
      (∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) - 4 * Real.pi)
      MeasureTheory.volume epsilon 1 :=
    hrectInt.sub continuousOn_const.intervalIntegrable
  have hfirstMono := intervalIntegral.integral_mono_on hepsilonOne hleftInt hpositiveInt
    (fun x hx => ons_criticalSecond_positiveInner_rect_lower
      (hepsilon.trans_le hx.1) hx.2)
  rw [intervalIntegral.integral_sub hrectInt continuousOn_const.intervalIntegrable,
    intervalIntegral.integral_const] at hfirstMono
  norm_num only [smul_eq_mul] at hfirstMono
  have hfirst :
      (∫ x in epsilon..1,
        ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) - 4 * Real.pi ≤
      ∫ x in epsilon..1,
        ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
    have hepsNonneg := hepsilon.le
    nlinarith [Real.pi_pos]
  have htailInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume 1 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le honePi] using
      ons_criticalSecond_fixedInner_continuousOn
        (epsilon := 1) (delta := Real.pi) (a := 0) (b := Real.pi)
        zero_lt_one honePi le_rfl
  have htailPoint : ∀ x ∈ Set.Icc (1 : ℝ) Real.pi,
      -4 * Real.pi ≤
        ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
    intro x hx
    simpa using ons_criticalSecondKernel_interval_lower (zero_lt_one.trans_le hx.1)
      hx.2 Real.pi_pos.le
  have htailConst : IntervalIntegrable (fun _x : ℝ => -4 * Real.pi)
      MeasureTheory.volume 1 Real.pi := continuousOn_const.intervalIntegrable
  have htailMono := intervalIntegral.integral_mono_on honePi htailConst htailInt htailPoint
  rw [intervalIntegral.integral_const] at htailMono
  norm_num only [smul_eq_mul] at htailMono
  have hwholeInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon Real.pi := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (hepsilonOne.trans honePi)] using
      ons_criticalSecond_fixedInner_continuousOn
        (a := 0) (b := Real.pi) hepsilon (hepsilonOne.trans honePi) le_rfl
  have hjoin := intervalIntegral.integral_add_adjacent_intervals hpositiveInt htailInt
  have hrect := ons_criticalSecond_rectCutoff_lower n
  change -12 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y at hrect
  nlinarith [Real.pi_pos, sq_nonneg (Real.pi - 1)]


theorem ons_criticalSecond_positiveQuadrantCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..Real.pi,
          ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono ons_criticalSecond_positiveQuadrantCutoff_lower
  have hbase : Filter.Tendsto (fun n : ℕ => (32 / 5 : ℝ) * (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  exact tendsto_const_nhds.add_atTop hbase

theorem ons_logGIntBetaDeriv2_neg_left (beta x y : ℝ) :
    ons_logGIntBetaDeriv2 beta (-x) y = ons_logGIntBetaDeriv2 beta x y := by
  simp [ons_logGIntBetaDeriv2, ons_gIntBetaDeriv2, ons_gIntBetaDeriv,
    ons_gInt, Real.cos_neg]

theorem ons_logGIntBetaDeriv2_neg_right (beta x y : ℝ) :
    ons_logGIntBetaDeriv2 beta x (-y) = ons_logGIntBetaDeriv2 beta x y := by
  simp [ons_logGIntBetaDeriv2, ons_gIntBetaDeriv2, ons_gIntBetaDeriv,
    ons_gInt, Real.cos_neg]

theorem ons_criticalSecond_inner_full_eq_two {x : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    (∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv2 ons_betaC x y) =
      2 * ∫ y in 0..Real.pi,
        ons_logGIntBetaDeriv2 ons_betaC x y := by
  let f : ℝ → ℝ := fun y => ons_logGIntBetaDeriv2 ons_betaC x y
  have hneg : (∫ y in (-Real.pi)..0, f y) = ∫ y in 0..Real.pi, f y := by
    have hchange := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) f
    have heven : (∫ y in 0..Real.pi, f (-y)) = ∫ y in 0..Real.pi, f y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact ons_logGIntBetaDeriv2_neg_right ons_betaC x y
    simpa only [neg_zero] using hchange.symm.trans heven
  have hleft := ons_criticalSecondKernel_intervalIntegrable hx hxpi
    (a := -Real.pi) (b := 0)
  have hright := ons_criticalSecondKernel_intervalIntegrable hx hxpi
    (a := 0) (b := Real.pi)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals hleft hright
  change (∫ y in (-Real.pi)..Real.pi, f y) = 2 * ∫ y in 0..Real.pi, f y
  linarith

theorem ons_criticalSecond_fullCutoff_eq_four (n : ℕ) :
    ((∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))),
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y) +
      ∫ x in Real.exp (-(n : ℝ))..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y) =
      4 * ∫ x in Real.exp (-(n : ℝ))..Real.pi,
        ∫ y in 0..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonPi : epsilon ≤ Real.pi := by
    have hepsilonOne : epsilon ≤ 1 := by
      change Real.exp (-(n : ℝ)) ≤ 1
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (Nat.cast_nonneg n)
    linarith [Real.pi_gt_three]
  let F : ℝ → ℝ := fun x =>
    ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y
  have hF_even (x : ℝ) : F (-x) = F x := by
    apply intervalIntegral.integral_congr
    intro y _hy
    exact ons_logGIntBetaDeriv2_neg_left ons_betaC x y
  have hneg : (∫ x in (-Real.pi)..(-epsilon), F x) =
      ∫ x in epsilon..Real.pi, F x := by
    have hchange := intervalIntegral.integral_comp_neg (a := epsilon) (b := Real.pi) F
    have heven : (∫ x in epsilon..Real.pi, F (-x)) = ∫ x in epsilon..Real.pi, F x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hF_even x
    linarith
  have hpos : (∫ x in epsilon..Real.pi, F x) =
      2 * ∫ x in epsilon..Real.pi,
        ∫ y in 0..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hepsilonPi] at hx
    exact ons_criticalSecond_inner_full_eq_two
      (hepsilon.trans_le hx.1) hx.2
  change (∫ x in (-Real.pi)..(-epsilon), F x) +
      (∫ x in epsilon..Real.pi, F x) = _
  rw [hneg, hpos]
  ring


theorem ons_criticalSecond_fullCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        (∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))),
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y) +
          ∫ x in Real.exp (-(n : ℝ))..Real.pi,
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  have hscale := ons_criticalSecond_positiveQuadrantCutoff_tendsto.const_mul_atTop
    (by norm_num : (0 : ℝ) < 4)
  apply hscale.congr'
  exact Filter.Eventually.of_forall fun n =>
    (ons_criticalSecond_fullCutoff_eq_four n).symm


theorem ons_cos_lt_one_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hne : x ≠ 0) :
    Real.cos x < 1 := by
  rcases hx with ⟨hxl, hxu⟩
  have hperiod := Real.cos_eq_one_iff_of_lt_of_lt
    (show -(2 * Real.pi) < x by linarith [Real.pi_pos])
    (show x < 2 * Real.pi by linarith [Real.pi_pos])
  have hcosne : Real.cos x ≠ 1 := by
    intro hcos
    exact hne (hperiod.mp hcos)
  exact lt_of_le_of_ne (Real.cos_le_one x) hcosne

theorem ons_criticalDenom_pos_of_mem_Icc_left {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hne : x ≠ 0) :
    0 < 2 - Real.cos x - Real.cos y := by
  have hxcos := ons_cos_lt_one_of_mem_Icc hx hne
  have hycos := Real.cos_le_one y
  linarith

theorem ons_criticalFirst_inner_integral (x : ℝ)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    (∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv ons_betaC x y) =
      (2 * Real.pi) * (2 * Real.cosh (2 * ons_betaC)) := by
  let c : ℝ := 2 * Real.cosh (2 * ons_betaC)
  have hconst : (∫ _y in (-Real.pi)..Real.pi, c) = (2 * Real.pi) * c := by
    rw [intervalIntegral.integral_const]
    norm_num only [smul_eq_mul]
    ring
  by_cases hx0 : x = 0
  · subst x
    have hyne : ∀ᵐ y : ℝ ∂MeasureTheory.volume, y ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {y : ℝ | ¬y ≠ 0} = ({0} : Set ℝ) := by
        ext y
        simp
      rw [hset]
      exact MeasureTheory.measure_singleton 0
    have heq : (∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC 0 y) =
        ∫ _y in (-Real.pi)..Real.pi, c := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hyne] with y hy0 hyI
      have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
        rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
        exact ⟨hyI.1.le, hyI.2⟩
      have hden : 2 - Real.cos 0 - Real.cos y ≠ 0 := by
        have hycos := ons_cos_lt_one_of_mem_Icc hyIcc hy0
        rw [Real.cos_zero]
        linarith
      simpa [c] using ons_logGIntBetaDeriv_betaC 0 y hden
    rw [heq, hconst]
  · have heq : (∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC x y) =
        ∫ _y in (-Real.pi)..Real.pi, c := by
      apply intervalIntegral.integral_congr
      intro y _hy
      have hden := (ons_criticalDenom_pos_of_mem_Icc_left hx hx0 (y := y)).ne'
      simpa [c] using ons_logGIntBetaDeriv_betaC x y hden
    rw [heq, hconst]

theorem ons_criticalFirst_double_integral :
    (∫ x in (-Real.pi)..Real.pi,
      ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC x y) =
      8 * Real.pi ^ 2 * Real.cosh (2 * ons_betaC) := by
  calc
    (∫ x in (-Real.pi)..Real.pi,
      ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC x y) =
        ∫ _x in (-Real.pi)..Real.pi,
          (2 * Real.pi) * (2 * Real.cosh (2 * ons_betaC)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
            exact ons_criticalFirst_inner_integral x hx
    _ = 8 * Real.pi ^ 2 * Real.cosh (2 * ons_betaC) := by
      rw [intervalIntegral.integral_const]
      norm_num only [smul_eq_mul]
      ring


theorem ons_criticalFirst_normalized_integral :
    (1 / (8 * Real.pi ^ 2)) *
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv ons_betaC x y) =
      Real.cosh (2 * ons_betaC) := by
  rw [ons_criticalFirst_double_integral]
  field_simp [Real.pi_ne_zero]

theorem ons_cosh_betaC_eq_sqrt_two :
    Real.cosh (2 * ons_betaC) = Real.sqrt 2 := by
  have hc := ons_cosh_betaC_sq
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hcpos := Real.cosh_pos (2 * ons_betaC)
  have hsnonneg := Real.sqrt_nonneg 2
  nlinarith

theorem ons_criticalFirst_normalized_integral_eq_sqrt_two :
    (1 / (8 * Real.pi ^ 2)) *
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv ons_betaC x y) = Real.sqrt 2 := by
  rw [ons_criticalFirst_normalized_integral, ons_cosh_betaC_eq_sqrt_two]


end StatMech.Onsager
