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
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (_hγ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  have hs : ∀ t, PSpace (M θ) (s t) := fun t =>
    ⟨(Random.Measurable_S h₁ t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable_A h₁ t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (r t) := fun t =>
    ⟨(Random.Measurable_R h₁ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace.of_process_path hs
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace.of_process_path ha
  have : PSpace (M θ) (AsPathRV.path r) :=
    PSpace.of_process_path hr
  𝔼[s, a, r : M θ](∑' t, γ ^ t * r t) =
    ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ) := by
-- proof
  intro _ _ _ _ _ _
  exact Expectation.ofRV_eq_integral
    (f := fun p : (ℕ → S) × (ℕ → A) × (ℕ → ℝ) => ∑' t, γ ^ t * p.2.2 t)
    (by
      refine (Measurable.tsum fun t => ?_).aestronglyMeasurable
      exact ((measurable_pi_apply t).comp measurable_snd |>.comp measurable_snd).const_mul _)


-- created on 2026-09-28
