import Lemma.Random.CondIndepJointS.of.All_Eq_Joint
import Lemma.Random.CondIndep.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.CondIndep.of.All_CondIndep.All_MeasurableJoint
import Notation.Probability.JointRv
import Notation.Fun
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random
open scoped ProbabilityTheory


/--
The current reward `r[t]` is conditionally independent of the history
`(s[:t], a[:t])` given the current state and action `(s[t], a[t])`.
This follows from the joint Markov property
[(s[t + 1], r[t]) ⟂ᵢ[M θ] (s[:t], a[:t]) | (s[t], a[t])](?module=Random.CondIndepJointS.of.All_Eq_Joint)
by projecting onto the reward coordinate.
-/
@[path]
private lemma reward
  [MeasurableSpace 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  [ReferenceMeasure 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t])) :
-- imply
  let : ∀ t, Measurable (s[t], a[t]) := fun t ↦ ((h₀ t) ▸ measurable_pi_apply t).snd
  r[t] ⟂ᵢ[M θ] (s[:t], a[:t]) | (s[t], a[t]) := by
-- proof
  intro
  apply (CondIndepJointS.of.All_Eq_Joint h₀).comp measurable_snd measurable_id

/--
State-transition Markov property of the unified trajectory model `M θ`:
the next state `s[t + 1]` is conditionally independent of the history
`(s[:t], a[:t])` given the current state and action `(s[t], a[t])`.
This follows from the joint Markov property
[(s[t + 1], r[t]) ⟂ᵢ[M θ] (s[:t], a[:t]) | (s[t], a[t])](?module=Random.CondIndepJointS.of.All_Eq_Joint)
by projecting onto the next-state coordinate.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  [ReferenceMeasure 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t])) :
-- imply
  let : ∀ t, Measurable (s[t], a[t]) := fun t ↦ ((h₀ t) ▸ measurable_pi_apply t).snd
  s[t + 1] ⟂ᵢ[M θ] (s[:t], a[:t]) | (s[t], a[t]) := by
-- proof
  intro
  apply (CondIndepJointS.of.All_Eq_Joint h₀).comp measurable_fst measurable_id

/--
Markov property of the continuous-action trajectory model `M θ`
(`Model`): given the next state `s[t+1]`, the future rewards
`r[t + 1:]` are conditionally independent of the current state-action pair `(s[t], a[t])`.
Built from the one-step Markov property
[(a n, r n, s (n + 1)) ⟂ᵢ[M θ] (r, s, a)[:n] | s n](?module=Random.CondIndep.of.All_Eq_Joint.All_EqWithDensity)
by
[r[t + 1:] ⟂ᵢ[π] (s t, a t) | s (t + 1)](?module=Random.CondIndep.of.All_CondIndep.All_MeasurableJoint).
-/
@[path]
private lemma future_reward
  [MeasurableSpace 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  [ReferenceMeasure 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t])) :
-- imply
  let : ∀ t, Measurable (r[t], s[t], a[t]) := fun t ↦ (h₀ t) ▸ measurable_pi_apply t
  r[t + 1:] ⟂ᵢ[M θ] (s[t], a[t]) | s[t + 1] :=
-- proof
  CondIndep.of.All_CondIndep.All_MeasurableJoint (fun t ↦ (h₀ t) ▸ measurable_pi_apply t)
    fun n ↦ CondIndep.of.All_Eq_Joint.All_EqWithDensity h₀ (n := n)


-- created on 2026-11-18
