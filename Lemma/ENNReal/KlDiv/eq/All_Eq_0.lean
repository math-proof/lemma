import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Initialize.Tactic.Attr.Basic
open Classical ENNReal InformationTheory MeasureTheory Real


private lemma kl_eq [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ ν : PMF α) :
  klDiv ν.toMeasure μ.toMeasure = if ∀ a, μ a = 0 → ν a = 0 then ENNReal.ofReal (∑ a, (ν a).toReal * log ((ν a).toReal / (μ a).toReal)) else ⊤ := by
  if h : ∀ a, μ a = 0 → ν a = 0 then
    rw [ite_eq_left h]
    let f : α → ℝ≥0∞ := fun a => if μ a = 0 then 0 else ν a / μ a
    have hf : Measurable f := measurable_of_finite f
    have hsing : ∀ a, (μ.toMeasure.withDensity f) {a} = ν a := by
      intro a
      rw [withDensity_apply f (measurableSet_singleton a), lintegral_singleton, μ.toMeasure_apply_singleton a (measurableSet_singleton a)]
      if h0 : μ a = 0 then
        simp [f, h0, h a h0]
      else
        have htop : μ a ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (μ.coe_le_one a) one_lt_top)
        simp [f, h0, ENNReal.div_mul_cancel h0 htop]
    have heqμ : ν.toMeasure = μ.toMeasure.withDensity f := by
      rw [← Measure.sum_smul_dirac ν.toMeasure, ← Measure.sum_smul_dirac (μ.toMeasure.withDensity f)]
      congr 1
      funext a
      rw [ν.toMeasure_apply_singleton a (measurableSet_singleton a), hsing a]
    have h_ac : ν.toMeasure ≪ μ.toMeasure := by
      intro s hs
      have hmeas : MeasurableSet s := by
        let t := Finset.univ.filter (fun a => a ∈ s)
        rw [show s = ⋃ a ∈ (t : Set α), ({a} : Set α) by ext a; simp [t]]
        exact MeasurableSet.biUnion t.countable_toSet fun _ _ => measurableSet_singleton _
      have hzero : ∀ a, μ.toMeasure {a} = 0 → ν.toMeasure {a} = 0 := by
        intro a ha
        rw [μ.toMeasure_apply_singleton a (measurableSet_singleton a)] at ha
        simpa [ν.toMeasure_apply_singleton a (measurableSet_singleton a)] using h a ha
      rw [← ν.toMeasure.sum_smul_dirac, Measure.sum_apply _ hmeas]
      refine ENNReal.tsum_eq_zero.mpr fun a => ?_
      rw [Measure.smul_apply, Measure.dirac_apply]
      if ha : a ∈ s then
        have hμa : μ.toMeasure {a} = 0 := le_antisymm (le_trans (measure_mono (Set.singleton_subset_iff.mpr ha)) (le_of_eq hs)) bot_le
        simp [ha, hzero a hμa]
      else
        simp [ha]
    have hrn : ν.toMeasure.rnDeriv μ.toMeasure =ᵐ[ν.toMeasure] f := (heqμ ▸ Measure.rnDeriv_withDensity μ.toMeasure hf).filter_mono h_ac.ae_le
    have hfin (g : α → ℝ) : Integrable g ν.toMeasure := by
      let C : ℝ := ∑ a, ‖g a‖
      refine Integrable.of_bound (measurable_of_finite g).aestronglyMeasurable C ?_
      exact Filter.Eventually.of_forall fun a => Finset.single_le_sum (fun b _ => norm_nonneg (g b)) (Finset.mem_univ a)
    have hint : Integrable (llr ν.toMeasure μ.toMeasure) ν.toMeasure := hfin _
    rw [klDiv_of_ac_of_integrable h_ac hint, measureReal_def, measureReal_def, measure_univ, measure_univ]
    simp
    congr 1
    have hintlog : Integrable (fun a => log (f a).toReal) ν.toMeasure := hfin _
    have hcongr : ∫ a, llr ν.toMeasure μ.toMeasure a ∂ν.toMeasure = ∫ a, log (f a).toReal ∂ν.toMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hrn] with a ha
      simp [llr, ha]
    rw [hcongr, integral_countable hintlog, tsum_fintype (L := SummationFilter.unconditional α)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [measureReal_def, ν.toMeasure_apply_singleton a (measurableSet_singleton a), smul_eq_mul]
    if h0 : μ a = 0 then
      have hν0 : ν a = 0 := h a h0
      simp [f, h0, hν0, Real.log_zero, _root_.div_zero]
    else
      simp [f, h0, ENNReal.toReal_div]
  else
    rw [ite_eq_right h, klDiv_of_not_ac]
    intro h_ac
    simp only [not_forall] at h
    obtain ⟨a, hμ0, hν0⟩ := h
    exact hν0 <| by
      have hnull : μ.toMeasure {a} = 0 := by
        rw [μ.toMeasure_apply_singleton a (measurableSet_singleton a), hμ0]
      simpa [ν.toMeasure_apply_singleton a (measurableSet_singleton a)] using h_ac hnull

/--
On a finite alphabet, the Kullback–Leibler divergence of two probability mass functions is the
explicit relative entropy. It is `⊤` when the first distribution charges an atom that the second
gives mass zero. This is the rate function of Sanov's theorem.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
-- given
  (μ ν : PMF α) :
-- imply
  klDiv ν.toMeasure μ.toMeasure = if ∀ a, μ a = 0 → ν a = 0 then ENNReal.ofReal (∑ a, (ν a).toReal * log ((ν a).toReal / (μ a).toReal)) else ⊤ :=
-- proof
  kl_eq μ ν


-- created on 2026-11-02
