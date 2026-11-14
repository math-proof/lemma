import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-!
# Closed-form value functions of the policy-gradient model with continuous states and continuous actions

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`).

The retired finite-action closed forms treated a general (e.g. continuous) state space with a finite action
space (`Policy` needs `[Fintype A]`: `π_θ(· | x)` is a probability vector).  Here the action space is a general
measurable space with a σ-finite reference measure `ReferenceMeasure.measure` (e.g. Lebesgue measure on `ℝ^m`),
and the policy `π_θ(u | x)` is a probability density of the action w.r.t. it (`DensityPolicy`); the environment is the
same `Env 𝒮 𝒜` (transition kernel `T(· | x, u)`, bounded reward kernel).

The conditional expectations `𝔼[· | s[t] = x]` of the sympy `Q_def`, `V_def` are taken
in the regular (kernel) sense; every finite action sum `∑ u, π_θ(u | x) * …` becomes the integral
`∫ u, π_θ(u | x) * … ∂ReferenceMeasure.measure`:

* `rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` (the reward clamped to `[-R, R]`, almost surely equal to it);
* `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]`;
* ;
* ;
* `P1kd θ p x y = ℙ(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p x u y du`, the density (w.r.t. the reference measure
  of `𝒮`) of the next state when `p x u` is the density of `M.env.trans (x, u)`.

The trajectory law `M.traj θ` / `M θ` is the Ionescu–Tulcea measure of the stage chain on `ℕ → ℝ × 𝒮 × 𝒜`,
built like `Model.traj` but with `DensityPolicy.kernel` (`Kernel.withDensity` of the reference measure of `𝒜`)
instead of `Policy.kernel` (`Kernel.ofFunOfCountable`).

These are the continuous-action counterparts of `Model.rk`, `Model.Wk`, `Model.Vk`, `Model.Qk`, `Model.P1k`;
the model is time-homogeneous, so none of them depends on `t`.
-/


namespace PolicyGradient

/-- A stochastic policy on a general (e.g. continuous) action space: `prob θ x u = π_θ(u | x)` is a probability density
of the action `a[t]` given the state `s[t] = x` w.r.t. the reference measure of `𝒜`
(continuous-action counterpart of `Policy`, whose `sum_eq_one` becomes `integral_eq_one`). -/
structure DensityPolicy (Θ 𝒮 𝒜 : Type*) [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜] where
  prob : Θ → 𝒮 → 𝒜 → ℝ
  nonneg : ∀ θ x u, 0 ≤ prob θ x u
  integral_eq_one : ∀ θ x, ∫ u, prob θ x u ∂(ReferenceMeasure.measure : Measure 𝒜) = 1
  measurable_prob : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => prob θ z.1 z.2)

/-- The policy-gradient model with a density policy on a general action space
(continuous-action counterpart of `Model`; the environment `Env 𝒮 𝒜` is unchanged). -/
structure DensityModel (Θ 𝒮 𝒜 : Type*) [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜] where
  env : Env 𝒮 𝒜
  policy : DensityPolicy Θ 𝒮 𝒜

end PolicyGradient
