import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.UrysohnsLemma
import Initialize.Tactic.Attr.Basic
open Classical ENNReal Filter MeasureTheory Real Set Topology


private lemma singular_close [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : ¬ ν ≪ μ) (M : ℝ) :
  ∃ f : α → ℝ, Continuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ M ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable α
  simp only [Measure.AbsolutelyContinuous, not_forall] at h
  obtain ⟨s, hμs, hνs⟩ := h
  obtain ⟨t, hst, ht, hμt⟩ := exists_measurable_superset_of_null hμs
  have hνt0 : ν t ≠ 0 := fun h0 => hνs (measure_mono_null hst h0)
  have hνt : 0 < ν t := lt_of_le_of_ne bot_le (Ne.symm hνt0)
  have hhalf : ν t / 2 < ν t := ENNReal.half_lt_self (ne_of_gt hνt) (measure_ne_top ν t)
  obtain ⟨F, hFt, hFclosed, hνF⟩ := ht.exists_lt_isClosed_of_ne_top (measure_ne_top ν t) hhalf
  have hμF : μ F = 0 := measure_mono_null hFt hμt
  have hp : 0 < (ν F).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨lt_trans (ENNReal.half_pos (ne_of_gt hνt)) hνF, (measure_ne_top ν F).lt_top⟩
  let p := (ν F).toReal
  let tℝ := max ((M + log 2) / p) 1
  have htpos : 0 < tℝ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have htp : M + log 2 ≤ tℝ * p := by
    if hle : (M + log 2) / p ≤ 1 then
      have ht1 : tℝ = 1 := max_eq_right hle
      rw [ht1, one_mul]
      exact (div_le_one hp).mp hle
    else
      have htq : tℝ = (M + log 2) / p := max_eq_left (le_of_not_ge hle)
      rw [htq, div_mul_cancel₀ _ hp.ne']
  have hμFlt : μ F < ENNReal.ofReal (exp (-tℝ)) := by
    rw [hμF]
    simpa using ENNReal.ofReal_pos.mpr (exp_pos (-tℝ))
  obtain ⟨U, hFU, hUopen, hμU⟩ := F.exists_isOpen_lt_of_lt _ hμFlt
  have hdisj : Disjoint Uᶜ F := by
    refine disjoint_left.mpr ?_
    intro x hxUc hxF
    exact hxUc (hFU hxF)
  obtain ⟨g, hg0, hg1, hgIcc⟩ :=
    exists_continuous_zero_one_of_isClosed hUopen.isClosed_compl hFclosed hdisj
  let f : α → ℝ := fun x => tℝ * g x
  have hf_cont : Continuous f := continuous_const.mul g.continuous
  have hf_bound : ∀ x, |f x| ≤ tℝ := by
    intro x
    have hg : 0 ≤ g x ∧ g x ≤ 1 := mem_Icc.mp (hgIcc x)
    rw [abs_of_nonneg (mul_nonneg htpos.le hg.1)]
    exact mul_le_of_le_one_right htpos.le hg.2
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x =>
    mul_nonneg htpos.le (mem_Icc.mp (hgIcc x)).1
  have hf_ge : ∀ x, F.indicator (fun _ => tℝ) x ≤ f x := by
    intro x
    if hx : x ∈ F then
      have hgx : g x = 1 := hg1 hx
      simp [f, hx, hgx]
    else
      simp [hx, hf_nonneg x]
  have hf_int : Integrable f ν :=
    Integrable.of_bound hf_cont.measurable.aestronglyMeasurable tℝ (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf_bound x)
  have hind_int : Integrable (F.indicator fun _ => tℝ) ν :=
    Integrable.of_bound (measurable_const.indicator (IsClosed.measurableSet hFclosed)).aestronglyMeasurable tℝ
      (Eventually.of_forall fun x => by
        if hx : x ∈ F then
          simp [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg htpos.le]
        else
          simpa [indicator_of_notMem hx, Real.norm_eq_abs, abs_zero] using htpos.le)
  have hint_ge : tℝ * p ≤ ∫ x, f x ∂ν := by
    refine le_trans ?_ (integral_mono hind_int hf_int hf_ge)
    rw [integral_indicator (IsClosed.measurableSet hFclosed), setIntegral_const, smul_eq_mul]
    simp [p, Measure.real, mul_comm]
  have hexp_le : ∀ x, exp (f x) ≤ exp tℝ * U.indicator (fun _ => (1 : ℝ)) x + Uᶜ.indicator (fun _ => 1) x := by
    intro x
    if hx : x ∈ U then
      have hfg : f x ≤ tℝ :=
        mul_le_of_le_one_right htpos.le (mem_Icc.mp (hgIcc x)).2
      have hU : U.indicator (fun _ => (1 : ℝ)) x = 1 := indicator_of_mem hx _
      have hUc : Uᶜ.indicator (fun _ => (1 : ℝ)) x = 0 := indicator_of_notMem (by simpa using hx) _
      rw [hU, hUc, mul_one, add_zero]
      exact exp_le_exp.mpr hfg
    else
      have hgx : g x = 0 := hg0 hx
      have hU : U.indicator (fun _ => (1 : ℝ)) x = 0 := indicator_of_notMem hx _
      have hUc : Uᶜ.indicator (fun _ => (1 : ℝ)) x = 1 := indicator_of_mem hx _
      simp [f, hgx, hU, hUc, exp_zero]
  have htoReal : (μ U).toReal ≤ exp (-tℝ) := by
    have hlt : μ U < ENNReal.ofReal (exp (-tℝ)) := hμU
    have hne : μ U ≠ ⊤ := measure_ne_top μ U
    apply le_of_lt
    rwa [ENNReal.lt_ofReal_iff_toReal_lt hne] at hlt
  have hexp_int : Integrable (fun x => exp (f x)) μ :=
    Integrable.of_bound (hf_cont.measurable.exp).aestronglyMeasurable (exp tℝ)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (le_trans (le_abs_self _) (hf_bound x)))
  have h1 : Integrable (fun x => exp tℝ * U.indicator (fun _ => (1 : ℝ)) x) μ :=
    ((Integrable.of_bound (measurable_const.indicator (IsOpen.measurableSet hUopen)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        if hx : x ∈ U then
          simp [indicator_of_mem hx]
        else
          simp [indicator_of_notMem hx])).const_mul (exp tℝ))
  have h2 : Integrable (Uᶜ.indicator fun _ => (1 : ℝ)) μ :=
    Integrable.of_bound (measurable_const.indicator (IsClosed.measurableSet hUopen.isClosed_compl)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        if hx : x ∈ Uᶜ then
          simp [indicator_of_mem hx]
        else
          simp [indicator_of_notMem hx])
  have hint_exp : ∫ x, exp (f x) ∂μ ≤ 2 := by
    have hsum : ∫ x, exp tℝ * U.indicator (fun _ => (1 : ℝ)) x + Uᶜ.indicator (fun _ => 1) x ∂μ = exp tℝ * (μ U).toReal + (μ Uᶜ).toReal := by
      rw [integral_add h1 h2, integral_const_mul,
        integral_indicator (IsOpen.measurableSet hUopen),
        integral_indicator (IsClosed.measurableSet hUopen.isClosed_compl),
        setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul]
      simp [Measure.real, mul_comm]
    refine le_trans (integral_mono hexp_int (h1.add h2) hexp_le) ?_
    have hfun : (fun x => exp tℝ * U.indicator (fun _ => (1 : ℝ)) x + Uᶜ.indicator (fun _ => 1) x) =
        (fun x => exp tℝ * U.indicator (fun _ => (1 : ℝ)) x) + Uᶜ.indicator (fun _ => 1) := by
      funext x
      rfl
    rw [← hfun, hsum]
    have hUle : exp tℝ * (μ U).toReal ≤ 1 := calc
      _ ≤ exp tℝ * exp (-tℝ) := mul_le_mul_of_nonneg_left htoReal (exp_pos _).le
      _ = 1 := by
        rw [← exp_add, add_neg_cancel, exp_zero]
    have hUcle : (μ Uᶜ).toReal ≤ 1 := by
      have hle : μ Uᶜ ≤ μ univ := measure_mono (subset_univ Uᶜ)
      rw [measure_univ] at hle
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
    linarith
  refine ⟨f, hf_cont, ⟨tℝ, hf_bound⟩, ?_⟩
  have hlog : log (∫ x, exp (f x) ∂μ) ≤ log 2 :=
    log_le_log (integral_exp_pos hexp_int) hint_exp
  linarith [hint_ge, hlog, htp]

/--
If a probability charges a null set of the reference, a bounded continuous test function makes the
Donsker–Varadhan expression larger than any prescribed real. Absolute continuity is therefore
necessary for the variational formula to stay finite, and it can be witnessed without leaving the
continuous functions.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
-- given
  (h : ¬ ν ≪ μ)
  (M : ℝ) :
-- imply
  ∃ f : α → ℝ, Continuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ M ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) :=
-- proof
  singular_close h M


-- created on 2026-11-02
