import Lemma.Random.Kf.eq.Integral
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
The iterated kernel expectation `Kf θ f j` of a bounded strongly measurable `f` is strongly measurable and bounded by the same constant.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ) :
-- imply
  StronglyMeasurable (M.Kf θ f j) ∧ ∀ z, ‖M.Kf θ f j z‖ ≤ C := by
-- proof
  induction j with
  | zero => exact ⟨hf, hC⟩
  | succ j ih =>
    refine ⟨?_, fun z => ?_⟩
    ·
      exact
        (funext fun z => (Kf.eq.Integral (M := M) (f := f) θ j z).symm) ▸
          (ih.1.comp_measurable measurable_snd).integral_kernel_prod_right' (κ := M.K θ)
    ·
      rw [Kf.eq.Integral (M := M) (f := f) θ j z]
      simpa using
        norm_integral_le_of_norm_le_const (μ := M.K θ z) (Filter.Eventually.of_forall ih.2)


-- created on 2026-10-07
