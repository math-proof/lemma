import Lemma.Random.Any_And_Any_All_LeAbsAndSubToRealKlDiv.le.Integral_Sub_Log_Integral_Exp.of.Gt_0.Integrable_Llr
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Initialize.Tactic.Attr.Basic
open BoundedContinuousFunction ENNReal Filter InformationTheory Interval MeasureTheory Random Set Topology Real


private lemma continuous_close [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (hint : Integrable (llr ν μ) ν) {ε : ℝ} (hε : 0 < ε) :
  ∃ f : α → ℝ, Continuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ (klDiv ν μ).toReal - ε ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable α
  obtain ⟨g, hg, ⟨C0, hC0⟩, hge⟩ :=
    Any_And_Any_All_LeAbsAndSubToRealKlDiv.le.Integral_Sub_Log_Integral_Exp.of.Gt_0.Integrable_Llr
      hνμ hint (half_pos hε)
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
  linarith [hge, (abs_le.mp hclose).1]

/--
On a Polish space, bounded continuous test functions approach the Kullback–Leibler divergence.
For every positive tolerance there is one whose Donsker–Varadhan expression sits at most that far
below the divergence, so the variational formula can be taken over continuous functions and the
rate is lower semicontinuous in the weak topology.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℝ}
-- given
  (hνμ : ν ≪ μ)
  (hint : Integrable (llr ν μ) ν)
  (hε : 0 < ε) :
-- imply
  ∃ f : α → ℝ, Continuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ (klDiv ν μ).toReal - ε ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) :=
-- proof
  continuous_close hνμ hint hε


-- created on 2026-11-02
