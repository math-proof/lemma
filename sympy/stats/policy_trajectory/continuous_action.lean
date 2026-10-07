import sympy.stats.policy_trajectory
import sympy.stats.rv
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Closed-form value functions of the policy-gradient model with continuous states and continuous actions

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`).

`sympy.stats.policy_trajectory.continuous` treats a general (e.g. continuous) state space with a finite action
space (`Policy` needs `[Fintype A]`: `π_θ(· | x)` is a probability vector).  Here the action space is a general
measurable space with a σ-finite reference measure `ReferenceMeasure.measure` (e.g. Lebesgue measure on `ℝ^m`),
and the policy `π_θ(u | x)` is a probability density of the action w.r.t. it (`DensityPolicy`); the environment is the
same `Env S A` (transition kernel `T(· | x, u)`, bounded reward kernel).

As in the continuous-state file, the conditional expectations `𝔼[· | s[t] = x]` of the sympy `Q_def`, `V_def` are taken
in the regular (kernel) sense; every finite action sum `∑ u, π_θ(u | x) * …` becomes the integral
`∫ u, π_θ(u | x) * … ∂ReferenceMeasure.measure`:

* `rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` (the reward clamped to `[-R, R]`, almost surely equal to it);
* `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]`;
* `Vkd θ γ x = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x] = ∑' k, γ ^ k * Wkd θ k x`;
* `Qkd θ γ x u = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x, a[t] = u] = rkd x u + γ * ∫ Vkd θ γ y ∂T(· | x, u)`;
* `P1kd θ p x y = Pr(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p x u y du`, the density (w.r.t. the reference measure
  of `S`) of the next state when `p x u` is the density of `M.env.trans (x, u)`.

These are the continuous-action counterparts of `Model.rk`, `Model.Wk`, `Model.Vk`, `Model.Qk`, `Model.P1k`
(`sympy.stats.policy_trajectory.continuous`); the model is time-homogeneous, so none of them depends on `t`.
-/
open MeasureTheory ProbabilityTheory

namespace PolicyGradient

/-- A stochastic policy on a general (e.g. continuous) action space: `prob θ x u = π_θ(u | x)` is a probability density
of the action `a[t]` given the state `s[t] = x` w.r.t. the reference measure of `A`
(continuous-action counterpart of `Policy`, whose `sum_eq_one` becomes `integral_eq_one`). -/
structure DensityPolicy (Θ S A : Type*) [ReferenceMeasure A] where
  prob : Θ → S → A → ℝ
  nonneg : ∀ θ x u, 0 ≤ prob θ x u
  integral_eq_one : ∀ θ x, ∫ u, prob θ x u ∂(ReferenceMeasure.measure : Measure A) = 1

/-- The policy-gradient model with a density policy on a general action space
(continuous-action counterpart of `Model`; the environment `Env S A` is unchanged). -/
structure DensityModel (Θ S A : Type*) [MeasurableSpace S] [ReferenceMeasure A] where
  env : Env S A
  pol : DensityPolicy Θ S A

namespace DensityModel

variable {Θ S A : Type*} [MeasurableSpace S] [ReferenceMeasure A]

/-- `rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]`, the expected reward clamped to `[-R, R]` -/
noncomputable def rkd (M : DensityModel Θ S A) (x : S) (u : A) : ℝ :=
  ∫ ρ, max (-M.env.R) (min M.env.R ρ) ∂(M.env.reward (x, u))

/-- `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]` with a density policy: one policy step (an integral over the actions) and one
transition per `k` -/
noncomputable def Wkd (M : DensityModel Θ S A) (θ : Θ) : ℕ → S → ℝ
  | 0 => fun x => ∫ u, M.pol.prob θ x u * M.rkd x u ∂ReferenceMeasure.measure
  | k + 1 => fun x => ∫ u, M.pol.prob θ x u * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure

/-- state value with a density policy: `Vkd θ γ x = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x] = ∑' k, γ ^ k * Wkd θ k x` -/
noncomputable def Vkd (M : DensityModel Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  ∑' k, γ ^ k * M.Wkd θ k x

/-- action value with a density policy:
`Qkd θ γ x u = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x, a[t] = u] = rkd x u + γ * ∫ y, Vkd θ γ y ∂T(· | x, u)` -/
noncomputable def Qkd (M : DensityModel Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  M.rkd x u + γ * ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u))

/-- `P1kd θ p x y = Pr(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p(y | x, u) du`, the next-state density
when `p x u` is a density of the transition `M.env.trans (x, u)` -/
noncomputable def P1kd (M : DensityModel Θ S A) (θ : Θ) (p : S → A → S → ℝ) (x y : S) : ℝ :=
  ∫ u, M.pol.prob θ x u * p x u y ∂ReferenceMeasure.measure

end DensityModel

end PolicyGradient
