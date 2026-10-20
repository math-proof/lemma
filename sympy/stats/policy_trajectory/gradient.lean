import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Definitions for the policy-gradient trajectory model

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`):

* `Pn θ n x y = Pr(s[t+n] = y | s[t] = x)` and `P1 θ x y = Pr(s[t+1] = y | s[t] = x)`;
* the time-free closed forms `Vc`, `Qc` of the state / action value functions.

All facts about these (Chapman–Kolmogorov, differentiability of the stage expectation / `Vc`, `Qc`, the gradient of the
Bellman equation, finite-sum forms of expectations, `V = Vc` on reachable states, …) live in
`Lemma/Random/*`, `Lemma/Tensor/*` and `Lemma/Real/*`; see the 2026-10-06 breaking-change entries
in `AGENTS.md` for the name maps.
-/
open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace PolicyGradient

namespace Model

variable {Θ S A : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- `Pn θ n x y = Pr(s[t+n] = y | s[t] = x)` (time-homogeneous `n`-step state transition) -/
noncomputable def Pn (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) : ℝ :=
  let z : ℝ × S × A → ℝ × S × A := id
  have : PSpace (M.stageK θ x) z := { aemeasurable := measurable_id.aemeasurable }
  𝔼[z : M.stageK θ x](M.Kf θ (fun w => if w.2.1 = y then (1:ℝ) else 0) n z)

/-- `P1 θ x y = Pr(s[t+1] = y | s[t] = x) = ∑ u, π_θ(u | x) * Pr(s' = y | x, u)` -/
noncomputable def P1 (M : Model Θ S A) (θ : Θ) (x y : S) : ℝ :=
  ∑ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y}

/-- Textbook state value (time-free closed form), matching local `V` in Lemma/Random:
`Vc θ γ x = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[0:] | s 0 = x)`,
where `(r t ω, s t ω, _) = ω t` on the trajectory space. -/
noncomputable def Vc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω => (ω t).2.1
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[0:] | s 0 = x)

/-- time-free closed form of the action-value function:
`Qc θ γ x u = 𝔼[ρ : reward(x,u)](clip ρ) + γ * 𝔼[y : trans(x,u)](Vc θ γ y)` -/
noncomputable def Qc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  have := M.env.reward_markov
  have := M.env.trans_markov
  let ρ : ℝ → ℝ := id
  have : PSpace (M.env.reward (x, u)) ρ := { aemeasurable := measurable_id.aemeasurable }
  let y : S → S := id
  have : PSpace (M.env.trans (x, u)) y := { aemeasurable := measurable_id.aemeasurable }
  𝔼[ρ : M.env.reward (x, u)](clip ρ (-M.env.R) M.env.R) +
    γ * 𝔼[y : M.env.trans (x, u)](M.Vc θ γ y)

end Model

end PolicyGradient
