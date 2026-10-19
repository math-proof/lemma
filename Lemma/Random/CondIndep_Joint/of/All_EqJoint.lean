import Lemma.Random.CondIndep.of.All_Eq_Joint
import Lemma.Random.CondIndep.of.All_CondIndep.All_MeasurableJoint
open MeasureTheory ProbabilityTheory PolicyGradient Random


/--
Markov property of the trajectory model `M θ`: given the next state `s[t+1]`, the future rewards `r[t+1:]`
are conditionally independent of the current state-action pair `(s[t], a[t])`.
It is built into `M θ`: the one-step Markov property `CondIndep.of.All_Eq_Joint` (history irrelevance of each step)
extends to the whole future by `CondIndep.of.All_CondIndep.All_MeasurableJoint`.
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
  (h₀ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  let h : ∀ t, Measurable (r t, s t, a t) := fun t ↦ (h₀ t) ▸ measurable_pi_apply t;
  r[t + 1:] ⟂ᵢ[M θ] (s t, a t) | s (t + 1) :=
-- proof
  CondIndep.of.All_CondIndep.All_MeasurableJoint (fun t ↦ (h₀ t) ▸ measurable_pi_apply t) fun n ↦ CondIndep.of.All_Eq_Joint h₀ (n := n)


-- created on 2026-10-08
-- updated on 2026-10-12
