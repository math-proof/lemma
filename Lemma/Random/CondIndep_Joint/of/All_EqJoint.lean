import Lemma.Random.CondIndep.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.CondIndep.of.All_CondIndep.All_MeasurableJoint
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Markov property of the discrete-state continuous-action trajectory model `M θ`
(`DensityModel` with finite `S` / `A`): given the next state `s[t+1]`, the future rewards
`r[t+1:]` are conditionally independent of the current state-action pair `(s[t], a[t])`.
Built from the dens one-step Markov property
`CondIndep.of.All_Eq_Joint.All_EqWithDensity` by
`CondIndep.of.All_CondIndep.All_MeasurableJoint`.
-/
@[path]
private lemma main
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S] [DecidableEq S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {θ : Θ}
  {t : ℕ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  let h : ∀ t, Measurable (r t, s t, a t) := fun t ↦ (h₀ t) ▸ measurable_pi_apply t;
  r[t + 1:] ⟂ᵢ[M θ] (s t, a t) | s (t + 1) :=
-- proof
  CondIndep.of.All_CondIndep.All_MeasurableJoint (fun t ↦ (h₀ t) ▸ measurable_pi_apply t)
    fun n ↦ CondIndep.of.All_Eq_Joint.All_EqWithDensity h₀ (n := n)


-- created on 2026-10-08
-- updated on 2026-11-04
