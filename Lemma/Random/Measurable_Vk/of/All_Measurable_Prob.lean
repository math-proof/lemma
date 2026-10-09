import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import Lemma.Random.Measurable_Wk.of.All_Measurable_Prob
open MeasureTheory PolicyGradient Random


/--
If every `x ↦ π_θ(u | x)` is measurable, so is the state value `x ↦ Vk θ γ x` on a general state space.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (h : ∀ θ u, Measurable (fun x => M.pol.prob θ x u))
  (θ : Θ)
  (γ : ℝ) :
-- imply
  Measurable (M.Vk θ γ) := by
-- proof
  apply Measurable.tsum fun k => (Measurable_Wk.of.All_Measurable_Prob (M := M) h θ k).const_mul _


-- created on 2026-10-07
