import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Initialize.Tactic.Attr.Basic
open BoundedContinuousFunction ENNReal Filter InformationTheory Interval MeasureTheory Set Topology Real


private lemma measurable_big [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (hint : ¬ Integrable (llr ν μ) ν) (M : ℝ) : ∃ f : α → ℝ, Measurable f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ M ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) := by
  let g : α → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hg_meas : Measurable g := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hg_int : Integrable g μ := by
    rw [← integrableOn_univ]
    simpa [g] using Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := μ) (s := univ)
      (by simp [measure_univ])
  have hg_one : ∫ x, g x ∂μ = 1 := by
    simpa [g, measureReal_def, measure_univ] using Measure.integral_toReal_rnDeriv hνμ
  have hllr_meas : Measurable (llr ν μ) := hg_meas.log
  have hprod_le : ∀ t : ℝ, 0 ≤ t → t * max (-log t) 0 ≤ 1 := by
    intro t ht
    if ht1 : t ≤ 1 then
      if ht0 : t = 0 then
        simp [ht0, log_zero, neg_zero, max_self, mul_zero]
      else
        have hlogn : log t ≤ 0 := log_nonpos ht ht1
        rw [max_eq_left (neg_nonneg.mpr hlogn)]
        have hmul : t * -log t = negMulLog t := by
          unfold negMulLog
          ring
        rw [hmul]
        exact (negMulLog_le_one_sub_self ht).trans (sub_le_self 1 ht)
    else
      have hgt : 1 < t := lt_of_not_ge ht1
      simp [max_eq_right (neg_nonpos.mpr (log_pos hgt).le), mul_zero]
  have hprod_int : Integrable (fun x => g x * max (-(llr ν μ x)) 0) μ := by
    refine Integrable.of_bound (hg_meas.mul ((hllr_meas.neg).max measurable_const)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    have hnn : 0 ≤ g x * max (-(llr ν μ x)) 0 :=
      mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _)
    rw [abs_of_nonneg hnn]
    exact hprod_le (g x) ENNReal.toReal_nonneg
  have hneg : Integrable (fun x => max (-(llr ν μ x)) 0) ν :=
    (integrable_toReal_rnDeriv_mul_iff hνμ).mp (by simpa [g] using hprod_int)
  have hpos : ¬ Integrable (fun x => max (llr ν μ x) 0) ν := by
    intro hp
    refine hint ((hp.sub hneg).congr (Eventually.of_forall fun x => ?_))
    simp only [Pi.sub_apply]
    if hx : 0 ≤ llr ν μ x then
      rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    else
      have hx' : llr ν μ x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), zero_sub, neg_neg]
  have hpos_lin : ∫⁻ x, ENNReal.ofReal (max (llr ν μ x) 0) ∂ν = ⊤ := by
    exact (not_ne_iff).mp ((lintegral_ofReal_ne_top_iff_integrable
      (hllr_meas.max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun x => le_max_right (llr ν μ x) (0 : ℝ))).not.mpr hpos)
  let f : ℕ → α → ℝ := fun n x => min (n : ℝ) (max (llr ν μ x) 0)
  have hf_meas : ∀ n, Measurable (f n) := fun n =>
    measurable_const.min ((hllr_meas).max measurable_const)
  have hf_nonneg : ∀ n x, 0 ≤ f n x := fun n x =>
    le_min (Nat.cast_nonneg n) (le_max_right _ _)
  have hf_bound : ∀ n x, |f n x| ≤ (n : ℝ) := by
    intro n x
    have hle : f n x ≤ (n : ℝ) := min_le_left _ _
    simpa [abs_of_nonneg (hf_nonneg n x)] using hle
  have hf_int : ∀ n, Integrable (f n) ν := fun n =>
    Integrable.of_bound (hf_meas n).aestronglyMeasurable (n : ℝ) (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf_bound n x)
  have hmono : Monotone fun n x => ENNReal.ofReal (f n x) := by
    intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min (Nat.cast_le.mpr hnm) le_rfl)
  have hfenn_meas : ∀ n, Measurable fun x => ENNReal.ofReal (f n x) := fun n =>
    (hf_meas n).ennreal_ofReal
  have hsup_eq : (fun x => ⨆ n, ENNReal.ofReal (f n x)) = fun x => ENNReal.ofReal (max (llr ν μ x) 0) := by
    ext x
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (max (llr ν μ x) 0)
    refine le_iSup_of_le n ?_
    simp only [f, min_eq_right hn]
    exact le_rfl
  have hlin_sup : ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂ν = ⊤ := by
    rwa [← lintegral_iSup hfenn_meas hmono, hsup_eq]
  have hexists : ∃ n, M + log 2 < ∫ x, f n x ∂ν := by
    have hnot : ¬ ∀ n, ∫ x, f n x ∂ν ≤ M + log 2 := by
      intro hall
      have hsuple : ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂ν ≤ ENNReal.ofReal (M + log 2) := by
        refine iSup_le fun n => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hf_int n) (Eventually.of_forall (hf_nonneg n))]
        exact ENNReal.ofReal_le_ofReal (hall n)
      simp only [hlin_sup] at hsuple
      exact lt_irrefl ⊤ (lt_of_le_of_lt hsuple ENNReal.ofReal_lt_top)
    obtain ⟨n, hn⟩ := not_forall.mp hnot
    exact ⟨n, not_le.mp hn⟩
  obtain ⟨n, hn⟩ := hexists
  have hexp_le : ∀ x, exp (f n x) ≤ max (g x) 1 := by
    intro x
    if hle : llr ν μ x ≤ 0 then
      have hf0 : f n x = 0 := by
        simp only [f, max_eq_right hle, min_eq_right (Nat.cast_nonneg n)]
      rw [hf0, exp_zero]
      exact le_max_right _ _
    else
      have hposll : 0 < llr ν μ x := lt_of_not_ge hle
      have hg0 : g x ≠ 0 := by
        intro h0
        have : llr ν μ x = 0 := by
          rw [llr]
          simp only [g] at h0
          rw [h0, log_zero]
        exact hposll.ne' this
      have hgpos : 0 < g x := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hg0)
      have hf : f n x = min (n : ℝ) (llr ν μ x) := by
        simp only [f, max_eq_left hposll.le]
      rw [hf, llr]
      exact ((exp_le_exp.mpr (min_le_right _ _)).trans (le_of_eq (exp_log hgpos))).trans (le_max_left _ _)
  have hexp_int : Integrable (fun x => exp (f n x)) μ :=
    Integrable.of_bound ((hf_meas n).exp).aestronglyMeasurable (exp (n : ℝ))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (min_le_left _ _))
  have hmax_int : Integrable (fun x => max (g x) 1) μ := by
    refine (hg_int.add (integrable_const 1)).mono (hg_meas.max measurable_const).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (le_max_of_le_right zero_le_one),
      abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg zero_le_one)]
    exact max_le (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  have hsum : ∫ x, g x + 1 ∂μ = 2 := by
    rw [integral_add hg_int (integrable_const 1), hg_one]
    simp [integral_const, measureReal_def, measure_univ]
    norm_num
  have hint_exp : ∫ x, exp (f n x) ∂μ ≤ 2 :=
    (integral_mono hexp_int hmax_int hexp_le).trans
      ((integral_mono hmax_int (hg_int.add (integrable_const 1)) fun x =>
        max_le (le_add_of_nonneg_right zero_le_one)
          (le_add_of_nonneg_left ENNReal.toReal_nonneg)).trans (le_of_eq hsum))
  have hlog : log (∫ x, exp (f n x) ∂μ) ≤ log 2 :=
    log_le_log (integral_exp_pos hexp_int) hint_exp
  refine ⟨f n, hf_meas n, ⟨(n : ℝ), hf_bound n⟩, ?_⟩
  linarith

private lemma continuous_lift [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {g : α → ℝ} (hg : Measurable g) {C0 : ℝ} (hC0 : ∀ x, |g x| ≤ C0) {ε : ℝ} (hε : 0 < ε) : ∃ f : α → ℝ, Continuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ (∫ x, g x ∂ν - log (∫ x, exp (g x) ∂μ)) - ε ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable α
  let C := max C0 0
  have hCnonneg : 0 ≤ C := le_max_right _ _
  have hC : ∀ x, |g x| ≤ C := fun x => le_trans (hC0 x) (le_max_left _ _)
  have hg_int : Integrable g (μ + ν) :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  have hexp_int : Integrable (fun x => exp (g x)) μ :=
    Integrable.of_bound (hg.exp).aestronglyMeasurable (exp C) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((abs_le.mp (hC x)).2))
  let I := ∫ x, exp (g x) ∂μ
  have hI : 0 < I := integral_exp_pos hexp_int
  let δ := min (ε / 4) (min (I / 2 * exp (-C)) (ε * I / 8 * exp (-C)))
  have hδ : 0 < δ := by
    refine lt_min (by linarith) (lt_min ?_ ?_)
    · exact mul_pos (div_pos hI two_pos) (exp_pos _)
    · exact mul_pos (div_pos (mul_pos hε hI) (by norm_num)) (exp_pos _)
  obtain ⟨φ, hφ, hφint⟩ := hg_int.exists_boundedContinuous_integral_sub_le hδ
  let f : α → ℝ := fun x => max (-C) (min (φ x) C)
  have hf_cont : Continuous f := continuous_const.max (φ.continuous.min continuous_const)
  have hf_bound : ∀ x, |f x| ≤ C := by
    intro x
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact le_max_left _ _
    · exact max_le (neg_le_self hCnonneg) (min_le_right _ _)
  have hdist : ∀ x, |f x - g x| ≤ |(φ : α → ℝ) x - g x| := by
    intro x
    if hup : C < φ x then
      have hf : f x = C := by
        simp only [f, min_eq_right (le_of_lt hup), max_eq_right (neg_le_self hCnonneg)]
      have hgC : g x ≤ C := (abs_le.mp (hC x)).2
      rw [hf, abs_of_nonneg (sub_nonneg.mpr hgC),
        abs_of_nonneg (sub_nonneg.mpr (le_trans hgC (le_of_lt hup)))]
      linarith
    else if hdown : φ x < -C then
      have hf : f x = -C := by
        simp only [f, min_eq_left (le_trans (le_of_lt hdown) (neg_le_self hCnonneg)),
          max_eq_left (le_of_lt hdown)]
      have hgC : -C ≤ g x := (abs_le.mp (hC x)).1
      rw [hf, abs_of_nonpos (sub_nonpos.mpr hgC),
        abs_of_nonpos (sub_nonpos.mpr (le_trans (le_of_lt hdown) hgC))]
      linarith
    else
      have hf : f x = φ x := by
        simp only [f, min_eq_left (le_of_not_gt hup), max_eq_right (le_of_not_gt hdown)]
      simp [hf]
  have hsub_int : Integrable (fun x => |(φ : α → ℝ) x - g x|) (μ + ν) :=
    (hφint.sub hg_int).norm
  have hνle : ν ≤ μ + ν := by
    intro s
    simp [Measure.add_apply]
  have hφabs : ∫ x, |(φ : α → ℝ) x - g x| ∂(μ + ν) ≤ δ := by
    simpa [Real.norm_eq_abs, abs_sub_comm] using hφ
  have hf_int_ν : Integrable (fun x => |f x - g x|) ν :=
    ((hsub_int.mono (by fun_prop) (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hdist x)).mono_measure hνle)
  have hsub_ν : ∫ x, |f x - g x| ∂ν ≤ δ :=
    (integral_mono hf_int_ν (hsub_int.mono_measure hνle) hdist).trans
      ((integral_mono_measure hνle (Eventually.of_forall fun _ => abs_nonneg _) hsub_int).trans
        hφabs)
  have hlip : ∀ x, |exp (f x) - exp (g x)| ≤ exp C * |f x - g x| := by
    intro x
    rw [← integral_exp, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    refine exp_le_exp.mpr ?_
    rw [Set.uIoc] at ht
    exact ((mem_Ioc.mp ht).2).trans (max_le ((abs_le.mp (hC x)).2) ((abs_le.mp (hf_bound x)).2))
  have hμle : μ ≤ μ + ν := by
    intro s
    simp [Measure.add_apply]
  have hf_meas : Measurable f := hf_cont.measurable
  have hf_int : Integrable f ν :=
    Integrable.of_bound hf_meas.aestronglyMeasurable C (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf_bound x)
  have hg_int_ν : Integrable g ν :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  have hexpf_int : Integrable (fun x => exp (f x)) μ :=
    Integrable.of_bound (hf_meas.exp).aestronglyMeasurable (exp C) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((abs_le.mp (hf_bound x)).2))
  have hsub_μ : Integrable (fun x => |f x - g x|) μ :=
    ((hsub_int.mono (by fun_prop) (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hdist x)).mono_measure hμle)
  have hfg_μ : ∫ x, |f x - g x| ∂μ ≤ δ :=
    (integral_mono hsub_μ (hsub_int.mono_measure hμle) hdist).trans
      ((integral_mono_measure hμle (Eventually.of_forall fun _ => abs_nonneg _) hsub_int).trans
        hφabs)
  have hexp_diff_int : Integrable (fun x => |exp (g x) - exp (f x)|) μ :=
    (hsub_μ.const_mul (exp C)).mono ((hg.exp.sub hf_meas.exp).aestronglyMeasurable.norm)
      (Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_sub_comm, abs_mul, abs_of_pos (exp_pos C)] using hlip x)
  let J := ∫ x, exp (f x) ∂μ
  have hIJgap : |I - J| ≤ exp C * δ := calc
    _ = |∫ x, exp (g x) - exp (f x) ∂μ| := by
      rw [integral_sub hexp_int hexpf_int]
    _ ≤ ∫ x, |exp (g x) - exp (f x)| ∂μ := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => exp (g x) - exp (f x))
    _ ≤ ∫ x, exp C * |f x - g x| ∂μ :=
      integral_mono hexp_diff_int (hsub_μ.const_mul (exp C)) (fun x => by
        simpa [abs_sub_comm] using hlip x)
    _ = exp C * ∫ x, |f x - g x| ∂μ := integral_const_mul (exp C) _
    _ ≤ exp C * δ := mul_le_mul_of_nonneg_left hfg_μ (exp_pos _).le
  have hδexp : exp C * δ ≤ I / 2 := by
    have hδle : δ ≤ I / 2 * exp (-C) := (min_le_right _ _).trans (min_le_left _ _)
    calc
      _ ≤ exp C * (I / 2 * exp (-C)) := mul_le_mul_of_nonneg_left hδle (exp_pos _).le
      _ = I / 2 := by
        rw [show exp C * (I / 2 * exp (-C)) = (exp C * exp (-C)) * (I / 2) by ring,
          ← exp_add, add_neg_cancel, exp_zero, one_mul]
  have hJhalf : I / 2 ≤ J := by
    have hgap : |I - J| ≤ I / 2 := hIJgap.trans hδexp
    linarith [abs_le.mp hgap]
  have hδlog : exp C * δ ≤ ε * I / 8 := by
    have hδle : δ ≤ ε * I / 8 * exp (-C) := (min_le_right _ _).trans (min_le_right _ _)
    calc
      _ ≤ exp C * (ε * I / 8 * exp (-C)) := mul_le_mul_of_nonneg_left hδle (exp_pos _).le
      _ = ε * I / 8 := by
        rw [show exp C * (ε * I / 8 * exp (-C)) = (exp C * exp (-C)) * (ε * I / 8) by ring,
          ← exp_add, add_neg_cancel, exp_zero, one_mul]
  have hlog : |log J - log I| ≤ ε / 4 := by
    have hJpos : 0 < J := lt_of_lt_of_le (div_pos hI two_pos) hJhalf
    have hratio : |log J - log I| ≤ 2 * |J - I| / I := by
      if hIJ : I ≤ J then
        have hpos : 0 < J / I := div_pos hJpos hI
        have hlogle : log (J / I) ≤ J / I - 1 := log_le_sub_one_of_pos hpos
        have hnonneg : 0 ≤ log J - log I := sub_nonneg.mpr (log_le_log hI hIJ)
        rw [← log_div hJpos.ne' hI.ne', abs_of_nonneg (by simpa [log_div hJpos.ne' hI.ne'] using hnonneg),
          abs_of_nonneg (sub_nonneg.mpr hIJ)]
        calc
          _ ≤ J / I - 1 := hlogle
          _ = (J - I) / I := by
            rw [div_sub_one hI.ne']
          _ ≤ 2 * (J - I) / I := by
            rw [div_le_div_iff_of_pos_right hI]
            nlinarith
      else
        have hJI : J ≤ I := le_of_not_ge hIJ
        have hpos : 0 < I / J := div_pos hI hJpos
        have hlogle : log (I / J) ≤ I / J - 1 := log_le_sub_one_of_pos hpos
        have hnonneg : 0 ≤ log I - log J := sub_nonneg.mpr (log_le_log hJpos hJI)
        rw [abs_sub_comm (log J) (log I), abs_sub_comm J I, ← log_div hI.ne' hJpos.ne',
          abs_of_nonneg (by simpa [log_div hI.ne' hJpos.ne'] using hnonneg),
          abs_of_nonneg (sub_nonneg.mpr hJI)]
        calc
          _ ≤ I / J - 1 := hlogle
          _ = (I - J) / J := by
            rw [div_sub_one hJpos.ne']
          _ ≤ 2 * (I - J) / I := by
            have hinv : (1 : ℝ) / J ≤ 2 / I := by
              rw [div_le_div_iff₀ hJpos hI]
              linarith [hJhalf]
            have hmul : (I - J) / J ≤ (I - J) * (2 / I) := by
              rw [show (I - J) / J = (I - J) * (1 / J) by ring]
              exact mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr hJI)
            simpa [show (I - J) * (2 / I) = 2 * (I - J) / I by ring] using hmul
    calc
      _ ≤ 2 * |J - I| / I := hratio
      _ = 2 * |I - J| / I := by
        rw [abs_sub_comm]
      _ ≤ 2 * (exp C * δ) / I := by
        rw [div_le_div_iff_of_pos_right hI]
        exact mul_le_mul_of_nonneg_left hIJgap (by norm_num)
      _ ≤ 2 * (ε * I / 8) / I := by
        rw [div_le_div_iff_of_pos_right hI]
        exact mul_le_mul_of_nonneg_left hδlog (by norm_num)
      _ = ε / 4 := by
        field_simp
        ring
  have hint_gap : |∫ x, f x ∂ν - ∫ x, g x ∂ν| ≤ ε / 4 := calc
    _ = |∫ x, f x - g x ∂ν| := by
      rw [integral_sub hf_int hg_int_ν]
    _ ≤ ∫ x, |f x - g x| ∂ν := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x - g x)
    _ ≤ δ := hsub_ν
    _ ≤ ε / 4 := min_le_left _ _
  have hclose : |(∫ x, f x ∂ν - log J) - (∫ x, g x ∂ν - log I)| ≤ ε / 2 := calc
    _ = |(∫ x, f x ∂ν - ∫ x, g x ∂ν) - (log J - log I)| := by
      congr 1
      ring_nf
    _ ≤ |∫ x, f x ∂ν - ∫ x, g x ∂ν| + |log J - log I| := by
      refine (abs_add_le (∫ x, f x ∂ν - ∫ x, g x ∂ν) (-(log J - log I))).trans ?_
      rw [abs_neg]
    _ ≤ ε / 4 + ε / 4 := add_le_add hint_gap hlog
    _ = ε / 2 := by
      ring
  refine ⟨f, hf_cont, ⟨C, hf_bound⟩, ?_⟩
  linarith [(abs_le.mp hclose).1]

/--
If the log-likelihood ratio is not integrable, a bounded continuous test function makes the
Donsker–Varadhan expression larger than any prescribed real. On a Polish space the variational
formula is therefore infinite exactly when `klDiv` is.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
-- given
  (hνμ : ν ≪ μ)
  (hint : ¬ Integrable (llr ν μ) ν)
  (M : ℝ) :
-- imply
  ∃ f : α → ℝ, Continuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ M ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) :=
-- proof
by
  obtain ⟨g, hg, ⟨C0, hC0⟩, hge⟩ := measurable_big hνμ hint (M + 1)
  obtain ⟨f, hf, hC, hle⟩ := continuous_lift (μ := μ) (ν := ν) hg hC0 one_pos
  refine ⟨f, hf, hC, ?_⟩
  linarith


-- created on 2026-11-02
