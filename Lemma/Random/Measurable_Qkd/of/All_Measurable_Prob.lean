import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.MeasurableRkd
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the action value `(x, u) ↦ Qkd θ γ x u`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
-- given
  (h : ∀ θ, Measurable (fun z : S × A => M.pol.prob θ z.1 z.2))
  (θ : Θ)
  (γ : ℝ) :
-- imply
  Measurable (fun z : S × A => M.Qkd θ γ z.1 z.2) := by
-- proof
  have := M.env.trans_markov
  apply (MeasurableRkd (M := M)).add (Measurable.const_mul _ γ)
  apply (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans) (f := fun z : (S × A) × S => M.Vkd θ γ z.2)
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) h θ γ).stronglyMeasurable.comp_measurable measurable_snd)).measurable


-- created on 2026-10-07
