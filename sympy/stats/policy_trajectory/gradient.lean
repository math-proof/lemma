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
  ∑ u, M.pol.prob θ x u * (M.env.trans (x, u)).real {y}

/-- time-free closed form of the state-value function: `Vc θ γ x = ∑' k, γ ^ k * 𝔼[r[t+k] | s[t] = x]` -/
noncomputable def Vc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  let rc := fun w : ℝ × S × A => clip w.1 (-M.env.R) M.env.R
  let W (j : ℕ) : ℝ :=
    let z : ℝ × S × A → ℝ × S × A := id
    have : PSpace (M.stageK θ x) z := { aemeasurable := measurable_id.aemeasurable }
    𝔼[z : M.stageK θ x](M.Kf θ rc j z)
  ∑' k, γ ^ k * W k

/-- time-free closed form of the action-value function:
`Qc θ γ x u = 𝔼[r | x, u] + γ * ∑ y, Pr(s' = y | x, u) * Vc θ γ y` -/
noncomputable def Qc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  (∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (x, u))) +
    γ * ∑ y, (M.env.trans (x, u)).real {y} * M.Vc θ γ y

end Model

end PolicyGradient
