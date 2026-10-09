import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


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
      show StronglyMeasurable (fun z => ∫ w, M.Kf θ f j w ∂(M.K θ z))
      exact (ih.1.comp_measurable measurable_snd).integral_kernel_prod_right' (κ := M.K θ)
    ·
      have h := norm_integral_le_of_norm_le_const (μ := M.K θ z) (Filter.Eventually.of_forall ih.2)
      show ‖∫ w, M.Kf θ f j w ∂(M.K θ z)‖ ≤ C
      simpa using h


-- created on 2026-10-07
