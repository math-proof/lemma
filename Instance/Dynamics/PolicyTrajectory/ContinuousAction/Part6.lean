import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-!
# Closed-form value functions of the policy-gradient model with continuous states and continuous actions

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`).

The retired finite-action closed forms treated a general (e.g. continuous) state space with a finite action
space (`Policy` needs `[Fintype 𝒜]`: `π_θ(· | x)` is a probability vector).  Here the action space is a general
measurable space with a σ-finite reference measure `ReferenceMeasure.measure` (e.g. Lebesgue measure on `ℝ^m`),
and the policy `π_θ(u | x)` is a probability density of the action w.r.t. it (`DensityPolicy`); the environment is the
same `Env 𝒮 𝒜` (transition kernel `T(· | x, u)`, bounded reward kernel).

The conditional expectations `𝔼[· | s[t] = x]` of the sympy `Q_def`, `V_def` are taken
in the regular (kernel) sense; every finite action sum `∑ u, π_θ(u | x) * …` becomes the integral
`∫ u, π_θ(u | x) * … ∂ReferenceMeasure.measure`:

* `rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` (the reward clamped to `[-R, R]`, almost surely equal to it);
* `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]`;
* `V0 θ γ x = ∑' k, γ ^ k * Wkd θ k x` and `V θ γ t s_t = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s_t)`;
* `Q θ γ t x u = 𝔼[(γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x ∧ a t = u]` and `Q0 θ γ x u = Q θ γ 0 x u`;
* `P1kd θ p x y = ℙ(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p x u y du`, the density (w.r.t. the reference measure
  of `𝒮`) of the next state when `p x u` is the density of `M.env.trans (x, u)`.

The trajectory law `M.traj θ` / `M θ` is the Ionescu–Tulcea measure of the stage chain on `ℕ → ℝ × 𝒮 × 𝒜`,
built like `Model.traj` but with `DensityPolicy.kernel` (`Kernel.withDensity` of the reference measure of `𝒜`)
instead of `Policy.kernel` (`Kernel.ofFunOfCountable`).

Finite-action discrete policies are the special case of this API with counting measure:
`Policy.toDensityPolicy` / `Model.toDensityModel` under `[CountableMeasure 𝒜]` turn `sum_eq_one` into
`integral_eq_one` against `Measure.count`, so `Wkd` / `V0` supersede the retired `Model.Wk` / `Model.V0`.
`DensityModel.IsConditionalProbability` applies on that counting case unchanged.
The model is time-homogeneous, so none of the closed forms depends on `t`.
-/


namespace PolicyGradient

variable {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]

namespace DensityModel.IsPolicyTrajectory

variable {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}

/-- Canonical projections form an `IsPolicyTrajectory` (`stage_eq` by `rfl`). -/
instance instCanonical (M : DensityModel Θ 𝒮 𝒜) :
    DensityModel.IsPolicyTrajectory M ⟨M.rewardAt⟩ ⟨M.stateAt⟩ ⟨M.actionAt⟩ where
  stage_eq t := by
    funext ω
    rfl

end DensityModel.IsPolicyTrajectory
end PolicyGradient
