import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Definitions for the policy-gradient trajectory model

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`):

* `Pn θ n x y = ℙ(s[t+n] = y | s[t] = x)` and `P1 θ x y = ℙ(s[t+1] = y | s[t] = x)`;
* the state / action value functions `V`, `Q` and their time-free forms `Vc`, `Qc`.

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

/-- `Pn θ n x y = ℙ(s[t+n] = y | s[t] = x)` (time-homogeneous `n`-step state transition) -/
noncomputable def Pn (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) : ℝ :=
  let z : ℝ × S × A → ℝ × S × A := id
  have : PSpace (M.stageK θ x) z := { aemeasurable := measurable_id.aemeasurable }
  𝔼[z : M.stageK θ x](M.Kf θ (fun w => if w.2.1 = y then (1:ℝ) else 0) n z)

/-- `P1 θ x y = ℙ(s[t+1] = y | s[t] = x) = ∑ u, π_θ(u | x) * ℙ(s' = y | x, u)` -/
noncomputable def P1 (M : Model Θ S A) (θ : Θ) (x y : S) : ℝ :=
  ∑ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y}

/-- State-value function:
`V θ γ t s_t = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = s_t)`,
where `(r t ω, s t ω, _) = ω t` on the trajectory space. -/
noncomputable def V (M : Model Θ S A) (θ : Θ) (γ : ℝ) (t : ℕ) (s_t : S) : ℝ :=
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω => (ω t).2.1
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = s_t)

/-- Time-free closed form of the state-value function: `Vc θ γ x = V θ γ 0 x`. -/
noncomputable def Vc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  M.V θ γ 0 x

/-- Action-value function:
`Q θ γ t s_t a_t = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = s_t ∧ a t = a_t)`,
where `(r t ω, s t ω, a t ω) = ω t` on the trajectory space. -/
noncomputable def Q (M : Model Θ S A) (θ : Θ) (γ : ℝ) (t : ℕ) (s_t : S) (a_t : A) : ℝ :=
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω => (ω t).2.1
  let a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω => (ω t).2.2
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = s_t ∧ a t = a_t)

/-- Time-free closed form of the action-value function: `Qc θ γ x u = Q θ γ 0 x u`. -/
noncomputable def Qc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  M.Q θ γ 0 x u

end Model

end PolicyGradient
