import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the state value `x ↦ Vkd θ γ x`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
-- given
  (h : ∀ θ, Measurable (fun z : S × A => M.pol.prob θ z.1 z.2))
  (θ : Θ)
  (γ : ℝ) :
-- imply
  Measurable (M.Vkd θ γ) := by
-- proof
  apply Measurable.tsum fun k => (Measurable_Wkd.of.All_Measurable_Prob (M := M) h θ k).const_mul _


-- created on 2026-10-07
