import sympy.vector.Basic
import Lemma.Random.CondIndep
import Lemma.Random.CondIndep.of.All_CondIndep.All_MeasurableJoint
open MeasureTheory ProbabilityTheory PolicyGradient Random


/--
Markov property of the trajectory model `M θ`: given the next state `s[t+1]`, the future rewards `r[t+1:]`
are conditionally independent of the current state-action pair `(s[t], a[t])`.
It is built into `M θ`: the one-step Markov property `Random.CondIndep` (history irrelevance of each step)
extends to the whole future by `Random.CondIndep.of.All_CondIndep.All_MeasurableJoint`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {θ : Θ}
  {t : ℕ}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  let h : ∀ t, Measurable (r t, s t, a t) := fun t ↦ (h₁ t) ▸ measurable_pi_apply t;
  r[t + 1:] ⟂ᵢ[M θ] (s t, a t) | s (t + 1) :=
-- proof
  CondIndep.of.All_CondIndep.All_MeasurableJoint (fun t ↦ (h₁ t) ▸ measurable_pi_apply t) fun n ↦ Random.CondIndep h₁ (n := n)

-- created on 2026-10-08
