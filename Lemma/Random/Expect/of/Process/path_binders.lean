import sympy.stats.policy_trajectory.gradient
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
open MeasureTheory PolicyGradient PolicyGradient.Model Random

set_option linter.unusedVariables false

/--
Sanity check: `𝔼[state, action, reward : M θ](…)` elaborates by flipping each process to its path RV
(`AsPathRV.process`) and taking their finite joint law.
-/
@[path]
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
    ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace hs
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace ha
  have : PSpace (M θ) (AsPathRV.path r) :=
    PSpace_Path.of.All_PSpace hr
  𝔼[r, s, a : M θ](∑' t, γ ^ t * r t) =
    ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ) := by
-- proof
  intro _ _ _ _ _ _
  exact Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A) => ∑' t, γ ^ t * p.1 t)
    (by
      refine (Measurable.tsum fun t => ?_).aestronglyMeasurable
      exact ((measurable_pi_apply t).comp measurable_fst).const_mul _)


-- created on 2026-09-28
