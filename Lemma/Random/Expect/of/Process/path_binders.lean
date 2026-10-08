import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Measurable_R
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory PolicyGradient PolicyGradient.Model Random

set_option linter.unusedVariables false

/--
Sanity check: `𝔼[state, action, reward : M θ](…)` elaborates by flipping each process to its path RV
(`AsPathRV.process`) and taking their finite joint law.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
-- given
  (_hγ : γ ∈ Set.Ico 0 1) :
-- imply
  have hs : ∀ t, PSpace (M θ) (state (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_S t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (action (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_A t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (reward (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_R t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path (state (S := S) (A := A))) :=
    PSpace.of_process_path hs
  have : PSpace (M θ) (AsPathRV.path (action (S := S) (A := A))) :=
    PSpace.of_process_path ha
  have : PSpace (M θ) (AsPathRV.path (reward (S := S) (A := A))) :=
    PSpace.of_process_path hr
  𝔼[state, action, reward : M θ](∑' t, γ ^ t * reward t) =
    ∫ ω, ∑' t, γ ^ t * reward t ω ∂(M θ) := by
-- proof
  intro _ _ _ _ _ _
  exact Expectation.ofRV_eq_integral
    (f := fun p : (ℕ → S) × (ℕ → A) × (ℕ → ℝ) => ∑' t, γ ^ t * p.2.2 t)
    (by
      refine (Measurable.tsum fun t => ?_).aestronglyMeasurable
      exact ((measurable_pi_apply t).comp measurable_snd |>.comp measurable_snd).const_mul _)


-- created on 2026-09-28
