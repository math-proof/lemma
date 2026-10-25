/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingCriticalLogBound_intervalIntegrable
    {m J b : Real} :
    IntervalIntegrable (triangularIsingCriticalLogBound m J b)
      volume (-Real.pi) Real.pi := by
  have hmer : MeromorphicOn (fun y : Real => 1 - Real.cos y)
      [[-Real.pi, Real.pi]] :=
    (analyticOnNhd_const.sub Real.analyticOnNhd_cos).meromorphicOn
  have hlog : IntervalIntegrable
      (fun y : Real => |Real.log (1 - Real.cos y)|)
      volume (-Real.pi) Real.pi := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      (hmer.intervalIntegrable_log).norm
  unfold triangularIsingCriticalLogBound
  exact (intervalIntegral.intervalIntegrable_const.add
    intervalIntegral.intervalIntegrable_const).add hlog

theorem triangularIsing_logSymbol_abs_le_criticalLogBound
    {beta J m b x y : Real} (hm : 0 < m)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi) (hy0 : y ≠ 0)
    (hlower : m * ((b - beta) ^ 2 +
        ((1 - Real.cos x) + (1 - Real.cos y))) <=
      triangularIsingSymbol b b (b * J) x y) :
    |Real.log (triangularIsingSymbol b b (b * J) x y)| <=
      triangularIsingCriticalLogBound m J b y := by
  have hB0 : 0 <= 1 - Real.cos y := by linarith [Real.cos_le_one y]
  have hB : 0 < 1 - Real.cos y := by
    apply lt_of_le_of_ne hB0
    intro hz
    have hcos : Real.cos y = 1 := by linarith
    have habs : |y| <= Real.pi := abs_le.mpr hy
    exact hy0 ((Real.cos_eq_one_iff_of_lt_of_lt
      (by rw [abs_le] at habs; linarith [Real.pi_pos])
      (by rw [abs_le] at habs; linarith [Real.pi_pos])).mp hcos)
  have hbase : m * (1 - Real.cos y) <=
      triangularIsingSymbol b b (b * J) x y := by
    have hA : 0 <= 1 - Real.cos x := by linarith [Real.cos_le_one x]
    have hdelta : 0 <= (b - beta) ^ 2 := sq_nonneg _
    nlinarith [hlower]
  have hpos : 0 < triangularIsingSymbol b b (b * J) x y :=
    (mul_pos hm hB).trans_le hbase
  have hupper := triangularIsingSymbol_le_rayAbsBound J b x y
  have hC := triangularIsingRaySymbolAbsBound_pos J b
  have hlogLower := Real.log_le_log (mul_pos hm hB) hbase
  rw [Real.log_mul hm.ne' hB.ne'] at hlogLower
  have hlogUpper := Real.log_le_log hpos hupper
  rw [abs_le]
  constructor
  · unfold triangularIsingCriticalLogBound
    have hmabs := neg_abs_le (Real.log m)
    have hBabs := neg_abs_le (Real.log (1 - Real.cos y))
    have hCabs := abs_nonneg (Real.log (triangularIsingRaySymbolAbsBound J b))
    linarith
  · unfold triangularIsingCriticalLogBound
    have hCm := le_abs_self (Real.log (triangularIsingRaySymbolAbsBound J b))
    have hmabs := abs_nonneg (Real.log m)
    have hBabs := abs_nonneg (Real.log (1 - Real.cos y))
    linarith

theorem triangularIsingSymbol_pos_of_critical_local_bounds
    {beta J m K : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    {b x y : Real} (hb : b ∈ U)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    0 < triangularIsingSymbol b b (b * J) x y := by
  have hA : 0 < (1 - Real.cos x) + (1 - Real.cos y) := by
    have h := StatMech.Onsager.ons_criticalDenom_pos_of_mem_Icc_left
      hx hx0 (y := y)
    linarith
  have hlower := (hbounds b hb x y).1
  exact (mul_pos hm (by positivity :
    0 < (b - beta) ^ 2 + ((1 - Real.cos x) + (1 - Real.cos y)))).trans_le
    hlower

theorem continuous_triangularIsing_log_right_of_critical_local_bounds
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y =>
      Real.log (triangularIsingSymbol b b (b * J) x y)) := by
  apply Continuous.log (by unfold triangularIsingSymbol; fun_prop)
  intro y
  exact (triangularIsingSymbol_pos_of_critical_local_bounds
    hm hbounds hb hx hx0 (y := y)).ne'

theorem continuous_triangularIsing_logDeriv_right_of_critical_local_bounds
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y => triangularIsingRayLogDeriv J b x y) := by
  unfold triangularIsingRayLogDeriv
  apply Continuous.div
  · unfold triangularIsingRaySymbolDeriv
    fun_prop
  · unfold triangularIsingSymbol
    fun_prop
  · intro y
    exact (triangularIsingSymbol_pos_of_critical_local_bounds
      hm hbounds hb hx hx0 (y := y)).ne'

theorem continuous_triangularIsing_criticalInnerLog
    {beta J m K b : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) :
    Continuous (fun x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (triangularIsingSymbol b b (b * J) x y)) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (triangularIsingCriticalLogBound m J b)
  · filter_upwards [] with x'
    exact (Real.measurable_log.comp (by
      unfold triangularIsingSymbol
      fun_prop)).aestronglyMeasurable
  · filter_upwards [] with x'
    filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      triangularIsing_logSymbol_abs_le_criticalLogBound hm hy hy0
        (hbounds b hb x' y).1
  · exact triangularIsingCriticalLogBound_intervalIntegrable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    have hB : 0 < 1 - Real.cos y := by
      have hB0 : 0 <= 1 - Real.cos y := by linarith [Real.cos_le_one y]
      apply lt_of_le_of_ne hB0
      intro hz
      have hcos : Real.cos y = 1 := by linarith
      have habs : |y| <= Real.pi := abs_le.mpr hy
      exact hy0 ((Real.cos_eq_one_iff_of_lt_of_lt
        (by rw [abs_le] at habs; linarith [Real.pi_pos])
        (by rw [abs_le] at habs; linarith [Real.pi_pos])).mp hcos)
    have hpos : 0 < triangularIsingSymbol b b (b * J) x y := by
      have hlower := (hbounds b hb x y).1
      have hxnonneg : 0 <= 1 - Real.cos x := by
        linarith [Real.cos_le_one x]
      have hsum : 0 < (b - beta) ^ 2 +
          ((1 - Real.cos x) + (1 - Real.cos y)) := by
        nlinarith [sq_nonneg (b - beta)]
      exact (mul_pos hm hsum).trans_le hlower
    have hc : ContinuousAt
        (fun x' => triangularIsingSymbol b b (b * J) x' y) x := by
      unfold triangularIsingSymbol
      fun_prop
    simpa only [Function.comp_apply] using hc.log hpos.ne'

theorem hasDerivAt_triangularIsing_criticalInnerIntegral
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt
      (fun t => ∫ y in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol t t (t * J) x y))
      (∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J b x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y => Real.log (triangularIsingSymbol t t (t * J) x y))
    (F' := fun t y => triangularIsingRayLogDeriv J t x y)
    (bound := triangularIsingCriticalFirstMajorant m K x) hs
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with t ht
    exact (continuous_triangularIsing_log_right_of_critical_local_bounds
      hm hbounds ht hx hx0).aestronglyMeasurable
  · exact (continuous_triangularIsing_log_right_of_critical_local_bounds
      hm hbounds hb hx hx0).intervalIntegrable _ _
  · exact (continuous_triangularIsing_logDeriv_right_of_critical_local_bounds
      hm hbounds hb hx hx0).aestronglyMeasurable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI t ht
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      triangularIsingRayLogDeriv_abs_le_criticalMajorant hm hK hx hy hx0 hy0
        (hbounds t ht x y).1 (hbounds t ht x y).2
  · exact triangularIsingCriticalFirstMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI t ht
    exact hasDerivAt_log_triangularIsingSymbol_along_ray
      (triangularIsingSymbol_pos_of_critical_local_bounds
        hm hbounds ht hx hx0 (y := y))

theorem triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable
    (J b : Real) :
    AEStronglyMeasurable
      (fun x => ∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J b x y)
      (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
  let mu := volume.restrict (Set.Ioc (-Real.pi) Real.pi)
  have hjoint : AEStronglyMeasurable
      (fun p : Real × Real => triangularIsingRayLogDeriv J b p.1 p.2)
      (mu.prod mu) := by
    apply Measurable.aestronglyMeasurable
    unfold triangularIsingRayLogDeriv triangularIsingRaySymbolDeriv
      triangularIsingSymbol
    fun_prop
  have hi := hjoint.integral_prod_right'
  have hpi : -Real.pi <= Real.pi := by linarith [Real.pi_pos]
  simpa only [mu, intervalIntegral.integral_of_le hpi,
    Set.uIoc_of_le hpi] using hi

theorem triangularIsing_criticalInnerLogDeriv_norm_le
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ‖∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J b x y‖ <=
      triangularIsingCriticalFirstOuterMajorant m K x := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun y => triangularIsingRayLogDeriv J b x y)
    (g := triangularIsingCriticalFirstMajorant m K x)
    (show -Real.pi <= Real.pi by linarith [Real.pi_pos]) (by
      filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
      have hy : y ∈ Set.Icc (-Real.pi) Real.pi := ⟨hyI.1.le, hyI.2⟩
      simpa only [Real.norm_eq_abs] using
        triangularIsingRayLogDeriv_abs_le_criticalMajorant
          hm hK hx hy hx0 hy0 (hbounds b hb x y).1 (hbounds b hb x y).2)
    (triangularIsingCriticalFirstMajorant_inner_intervalIntegrable x)
  rw [triangularIsingCriticalFirstMajorant_inner_integral] at hnorm
  exact hnorm

theorem hasDerivAt_triangularIsing_criticalDoubleIntegral
    {beta J m K b : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) :
    HasDerivAt
      (fun t => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol t t (t * J) x y))
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          triangularIsingRayLogDeriv J b x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (triangularIsingSymbol t t (t * J) x y))
    (F' := fun t x => ∫ y in (-Real.pi)..Real.pi,
      triangularIsingRayLogDeriv J t x y)
    (bound := triangularIsingCriticalFirstOuterMajorant m K) hs
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with t ht
    exact (continuous_triangularIsing_criticalInnerLog hm hbounds ht).aestronglyMeasurable
  · exact (continuous_triangularIsing_criticalInnerLog hm hbounds hb).intervalIntegrable _ _
  · exact triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable J b
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI t ht
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact triangularIsing_criticalInnerLogDeriv_norm_le
      hm hK hbounds ht hx hx0
  · exact triangularIsingCriticalFirstOuterMajorant_intervalIntegrable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI t ht
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact hasDerivAt_triangularIsing_criticalInnerIntegral
      hm hK hUopen hbounds ht hx hx0

theorem continuousAt_triangularIsing_criticalInnerLogDeriv
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ContinuousAt
      (fun t => ∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J t x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (triangularIsingCriticalFirstMajorant m K x)
  · filter_upwards [hs] with t ht
    exact (continuous_triangularIsing_logDeriv_right_of_critical_local_bounds
      hm hbounds ht hx hx0).aestronglyMeasurable
  · filter_upwards [hs] with t ht
    filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      triangularIsingRayLogDeriv_abs_le_criticalMajorant
        hm hK hx hy hx0 hy0 (hbounds t ht x y).1 (hbounds t ht x y).2
  · exact triangularIsingCriticalFirstMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI
    have hpos := triangularIsingSymbol_pos_of_critical_local_bounds
      hm hbounds hb hx hx0 (y := y)
    unfold triangularIsingRayLogDeriv
    apply ContinuousAt.div
    · unfold triangularIsingRaySymbolDeriv
      fun_prop
    · unfold triangularIsingSymbol
      fun_prop
    · exact hpos.ne'

theorem continuousAt_triangularIsing_criticalDoubleLogDeriv
    {beta J m K b : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) :
    ContinuousAt
      (fun t => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          triangularIsingRayLogDeriv J t x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (triangularIsingCriticalFirstOuterMajorant m K)
  · exact Filter.Eventually.of_forall
      (triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable J)
  · filter_upwards [hs] with t ht
    filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact triangularIsing_criticalInnerLogDeriv_norm_le
      hm hK hbounds ht hx hx0
  · exact triangularIsingCriticalFirstOuterMajorant_intervalIntegrable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact continuousAt_triangularIsing_criticalInnerLogDeriv
      hm hK hUopen hbounds hb hx hx0


theorem triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root
    {beta J : Real} (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    ContDiffAt Real 1
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
  obtain ⟨U, hUnhds, hUopen, m, K, hm, hK, hbounds⟩ :=
    exists_triangularIsingCriticalRay_local_bounds hbeta hJ hroot
  let d : Real -> Real := fun b =>
    -(1 / (8 * Real.pi ^ 2)) *
      ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          triangularIsingRayLogDeriv J b x y
  let f' : Real -> Real →L[Real] Real := fun b =>
    d b • ContinuousLinearMap.id Real Real
  have hderiv : ∀ b ∈ U,
      HasDerivAt (fun t => triangularIsingFreeEnergyValue t t (t * J))
        (d b) b := by
    intro b hb
    have hdouble := hasDerivAt_triangularIsing_criticalDoubleIntegral
      hm hK hUopen hbounds hb
    unfold triangularIsingFreeEnergyValue
    have hconst := hasDerivAt_const b (-Real.log 2)
    have hscaled := hdouble.const_mul (1 / (8 * Real.pi ^ 2))
    simpa only [d, zero_sub, neg_mul] using hconst.sub hscaled
  rw [contDiffAt_one_iff]
  refine ⟨f', U, hUnhds, ?_, ?_⟩
  · have hd : ContinuousOn d U := by
      intro b hb
      exact (continuousAt_triangularIsing_criticalDoubleLogDeriv
        hm hK hUopen hbounds hb).const_mul
          (-(1 / (8 * Real.pi ^ 2))) |>.continuousWithinAt
    exact hd.smul continuousOn_const
  · intro b hb
    rw [hasFDerivAt_iff_hasDerivAt]
    simpa only [f', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hderiv b hb

theorem triangularIsingFreeEnergyValue_contDiffAt_one_of_nonnegative_root
    {beta J : Real} (hbeta : 0 < beta) (hJ : 0 <= J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    ContDiffAt Real 1
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root
    hbeta (by linarith) hroot

end
end StatMech.FrontierA
