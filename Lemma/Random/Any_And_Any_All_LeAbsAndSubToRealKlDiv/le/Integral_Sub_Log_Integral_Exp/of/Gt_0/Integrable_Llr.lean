import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Initialize.Tactic.Attr.Basic
open Classical ENNReal Filter InformationTheory MeasureTheory Real Set Topology


private lemma close [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (hint : Integrable (llr ν μ) ν) {ε : ℝ} (hε : 0 < ε) :
  ∃ f : α → ℝ, Measurable f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ (klDiv ν μ).toReal - ε ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) := by
  let g : α → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hg_meas : Measurable g := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hg_int : Integrable g μ := by
    rw [← integrableOn_univ]
    simpa [g] using Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := μ) (s := univ)
      (by simp [measure_univ])
  have hg_one : ∫ x, g x ∂μ = 1 := by
    simpa [g, measureReal_def, measure_univ] using Measure.integral_toReal_rnDeriv hνμ
  let A : ℕ → Set α := fun n => {x | g x ≤ exp (-(n : ℝ))}
  have hA : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le hg_meas measurable_const
  let f : ℕ → α → ℝ := fun n =>
    (A n).piecewise (fun _ => -(n : ℝ)) (fun x => min (n : ℝ) (llr ν μ x))
  have hllr_meas : Measurable (llr ν μ) := hg_meas.log
  have hf_meas : ∀ n, Measurable (f n) := fun n =>
    Measurable.piecewise (hA n) measurable_const (measurable_const.min hllr_meas)
  have hbound : ∀ n x, |f n x| ≤ n := by
    intro n x
    if hx : x ∈ A n then
      have : f n x = -(n : ℝ) := by
        simpa [f] using Set.piecewise_eq_of_mem (A n) (fun _ => -(n : ℝ))
          (fun x => min (n : ℝ) (llr ν μ x)) hx
      rw [this]
      simp [abs_neg, abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
    else
      have hgt : exp (-(n : ℝ)) < g x := lt_of_not_ge (by simpa [A] using hx)
      have hlog : -(n : ℝ) < llr ν μ x := by
        rw [llr]
        have hlog_exp : log (exp (-(n : ℝ))) < log (g x) := log_lt_log (exp_pos _) hgt
        simpa [log_exp] using hlog_exp
      have hmin_ge : -(n : ℝ) ≤ min (n : ℝ) (llr ν μ x) :=
        le_min (neg_le_self (Nat.cast_nonneg n)) (le_of_lt hlog)
      have hmin_le : min (n : ℝ) (llr ν μ x) ≤ n := min_le_left _ _
      have : f n x = min (n : ℝ) (llr ν μ x) := by
        simpa [f] using Set.piecewise_eq_of_notMem (A n) (fun _ => -(n : ℝ))
          (fun x => min (n : ℝ) (llr ν μ x)) hx
      simpa [this] using abs_le.mpr ⟨by linarith, hmin_le⟩
  have hdom : ∀ n, ∀ᵐ x ∂ν, ‖f n x‖ ≤ |llr ν μ x| := by
    intro n
    filter_upwards [Measure.rnDeriv_pos hνμ,
      (Measure.rnDeriv_lt_top ν μ).filter_mono hνμ.ae_le] with x hpos htop
    have hgp : 0 < g x := ENNReal.toReal_pos hpos.ne' htop.ne
    have habs_llr : |f n x| ≤ |llr ν μ x| := by
      if hx : x ∈ A n then
        have : f n x = -(n : ℝ) := by
          simpa [f] using Set.piecewise_eq_of_mem (A n) (fun _ => -(n : ℝ))
            (fun x => min (n : ℝ) (llr ν μ x)) hx
        have hll : llr ν μ x ≤ -(n : ℝ) := by
          rw [llr]
          have hgx : g x ≤ exp (-(n : ℝ)) := by simpa [A] using hx
          simpa [llr, log_exp] using log_le_log hgp hgx
        rw [this, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
        have : (n : ℝ) ≤ |llr ν μ x| := by
          rw [abs_of_nonpos (le_trans hll (neg_nonpos_of_nonneg (Nat.cast_nonneg n)))]
          linarith
        exact this
      else
        have : f n x = min (n : ℝ) (llr ν μ x) := by
          simpa [f] using Set.piecewise_eq_of_notMem (A n) (fun _ => -(n : ℝ))
            (fun x => min (n : ℝ) (llr ν μ x)) hx
        rw [this]
        have hgt : exp (-(n : ℝ)) < g x := lt_of_not_ge (by simpa [A] using hx)
        have hlog : -(n : ℝ) < log (g x) := by
          rw [← log_exp (-(n : ℝ))]
          exact log_lt_log (exp_pos _) hgt
        have hll : llr ν μ x = log (g x) := rfl
        rw [hll]
        if hposll : 0 ≤ log (g x) then
          have : 0 ≤ min (n : ℝ) (log (g x)) := le_min (Nat.cast_nonneg n) hposll
          simp [abs_of_nonneg this, abs_of_nonneg hposll]
        else
          have hneg : log (g x) < 0 := lt_of_not_ge hposll
          have hmin_eq : min (n : ℝ) (log (g x)) = log (g x) :=
            min_eq_right (le_of_lt (lt_of_lt_of_le hneg (Nat.cast_nonneg n)))
          simp [hmin_eq]
    simpa [Real.norm_eq_abs] using habs_llr
  have hlim_ae : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (𝓝 (llr ν μ x)) := by
    filter_upwards [Measure.rnDeriv_pos hνμ,
      (Measure.rnDeriv_lt_top ν μ).filter_mono hνμ.ae_le] with x hpos htop
    have hgp : 0 < g x := ENNReal.toReal_pos hpos.ne' htop.ne
    obtain ⟨N1, hN1⟩ := exists_nat_gt |llr ν μ x|
    obtain ⟨N2, hN2⟩ := exists_nat_gt (-log (g x))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max N1 N2)] with n hn
    have hcast1 : |llr ν μ x| < (n : ℝ) :=
      lt_of_lt_of_le hN1 (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
    have hcast2 : -log (g x) < (n : ℝ) :=
      lt_of_lt_of_le hN2 (Nat.cast_le.mpr (le_trans (le_max_right _ _) hn))
    have hxA : x ∉ A n := by
      have : exp (-(n : ℝ)) < g x := by
        have : -(n : ℝ) < log (g x) := by linarith
        simpa [exp_log hgp] using exp_lt_exp.mpr this
      simpa [A] using this
    have hmin : min (n : ℝ) (llr ν μ x) = llr ν μ x :=
      min_eq_right (le_of_lt (abs_lt.mp hcast1).2)
    simpa [f, hmin] using (Set.piecewise_eq_of_notMem (A n) (fun _ => -(n : ℝ))
      (fun y => min (n : ℝ) (llr ν μ y)) hxA).symm
  have hint_f : Tendsto (fun n => ∫ x, f n x ∂ν) atTop (𝓝 (∫ x, llr ν μ x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => |llr ν μ x|)
      (fun n => (hf_meas n).aestronglyMeasurable) hint.norm hdom hlim_ae
  have hdom_exp : ∀ n x, ‖exp (f n x)‖ ≤ max (g x) 1 := by
    intro n x
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    if hx : x ∈ A n then
      have hfx : f n x = -(n : ℝ) := by
        simpa [f] using Set.piecewise_eq_of_mem (A n) (fun _ => -(n : ℝ))
          (fun y => min (n : ℝ) (llr ν μ y)) hx
      rw [hfx]
      exact le_trans ((exp_le_exp.mpr (neg_nonpos_of_nonneg (Nat.cast_nonneg n))).trans_eq exp_zero)
        (le_max_right (g x) 1)
    else
      have hfx : f n x = min (n : ℝ) (llr ν μ x) := by
        simpa [f] using Set.piecewise_eq_of_notMem (A n) (fun _ => -(n : ℝ))
          (fun y => min (n : ℝ) (llr ν μ y)) hx
      have hgt : exp (-(n : ℝ)) < g x := lt_of_not_ge (by simpa [A] using hx)
      simpa [hfx, llr] using
        (((exp_le_exp.mpr (min_le_right (n : ℝ) (log (g x)))).trans
          (le_of_eq (exp_log (lt_trans (exp_pos _) hgt)))).trans (le_max_left (g x) 1))
  have hmax_int : Integrable (fun x => max (g x) 1) μ := by
    refine (hg_int.add (integrable_const 1)).mono (hg_meas.max measurable_const).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (le_max_of_le_right zero_le_one),
      abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg zero_le_one)]
    exact max_le (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  have hlim_exp : ∀ x, Tendsto (fun n => exp (f n x)) atTop (𝓝 (g x)) := by
    intro x
    if hg0 : g x = 0 then
      have hmem : ∀ n, x ∈ A n := fun n => by simpa [A, hg0] using (exp_pos (-(n : ℝ))).le
      have hfneg : ∀ n, f n x = -(n : ℝ) := fun n => by
        simpa [f] using Set.piecewise_eq_of_mem (A n) (fun _ => -(n : ℝ))
          (fun y => min (n : ℝ) (llr ν μ y)) (hmem n)
      have htend : Tendsto (fun n : ℕ => exp (-(n : ℝ))) atTop (𝓝 0) :=
        tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      simpa [hg0, hfneg] using htend
    else
      have hgp : 0 < g x := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hg0)
      obtain ⟨N1, hN1⟩ := exists_nat_gt |llr ν μ x|
      obtain ⟨N2, hN2⟩ := exists_nat_gt (-log (g x))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max N1 N2)] with n hn
      have hcast1 : |llr ν μ x| < (n : ℝ) :=
        lt_of_lt_of_le hN1 (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
      have hcast2 : -log (g x) < (n : ℝ) :=
        lt_of_lt_of_le hN2 (Nat.cast_le.mpr (le_trans (le_max_right _ _) hn))
      have hxA : x ∉ A n := by
        have : exp (-(n : ℝ)) < g x := by
          have : -(n : ℝ) < log (g x) := by linarith
          simpa [exp_log hgp] using exp_lt_exp.mpr this
        simpa [A] using this
      have hmin : min (n : ℝ) (llr ν μ x) = llr ν μ x :=
        min_eq_right (le_of_lt (abs_lt.mp hcast1).2)
      have hfeq : f n x = llr ν μ x := by
        simpa [f, hmin] using Set.piecewise_eq_of_notMem (A n) (fun _ => -(n : ℝ))
          (fun y => min (n : ℝ) (llr ν μ y)) hxA
      rw [hfeq, llr]
      exact (exp_log hgp).symm
  have hexp_tendsto : Tendsto (fun n => ∫ x, exp (f n x) ∂μ) atTop (𝓝 1) := by
    simpa [hg_one] using tendsto_integral_of_dominated_convergence (fun x => max (g x) 1)
      (fun n => ((hf_meas n).exp).aestronglyMeasurable) hmax_int
      (fun n => Eventually.of_forall (hdom_exp n)) (Eventually.of_forall hlim_exp)
  have hlog_tendsto : Tendsto (fun n => log (∫ x, exp (f n x) ∂μ)) atTop (𝓝 0) := by
    change Tendsto (log ∘ fun n => ∫ x, exp (f n x) ∂μ) atTop (𝓝 0)
    simpa [log_one] using (continuousAt_log one_ne_zero).tendsto.comp hexp_tendsto
  have hkl : (klDiv ν μ).toReal = ∫ x, llr ν μ x ∂ν :=
    toReal_klDiv_of_measure_eq hνμ (by simp [measure_univ])
  have hexpr : Tendsto (fun n => (∫ x, f n x ∂ν) - log (∫ x, exp (f n x) ∂μ)) atTop
      (𝓝 ((klDiv ν μ).toReal)) := by
    simpa [hkl] using hint_f.sub hlog_tendsto
  obtain ⟨n, hn⟩ := (hexpr.eventually (Metric.ball_mem_nhds _ hε)).exists
  refine ⟨f n, hf_meas n, ⟨(n : ℝ), hbound n⟩, ?_⟩
  exact le_of_lt (by linarith [abs_lt.mp (by simpa [Real.dist_eq] using hn)])

/--
Bounded measurable test functions approach the Kullback–Leibler divergence. For every positive
tolerance there is one whose Donsker–Varadhan expression sits at most that far below the divergence.
Together with the matching upper bound, this is the variational formula for the rate in Sanov's
theorem.
-/
@[path]
private lemma main
  [MeasurableSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℝ}
-- given
  (hνμ : ν ≪ μ)
  (hint : Integrable (llr ν μ) ν)
  (hε : 0 < ε) :
-- imply
  ∃ f : α → ℝ, Measurable f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ (klDiv ν μ).toReal - ε ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) :=
-- proof
  close hνμ hint hε


-- created on 2026-11-02
