import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Structure.Dynamics.PolicyTrajectory.ContinuousAction.Part2
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-!
# Closed-form value functions of the policy-gradient model with continuous states and continuous actions

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`).

`Def.Dynamics.PolicyTrajectory.Continuous` treats a general (e.g. continuous) state space with a finite action
space (`Policy` needs `[Fintype A]`: `π_θ(· | x)` is a probability vector).  Here the action space is a general
measurable space with a σ-finite reference measure `ReferenceMeasure.measure` (e.g. Lebesgue measure on `ℝ^m`),
and the policy `π_θ(u | x)` is a probability density of the action w.r.t. it (`DensityPolicy`); the environment is the
same `Env S A` (transition kernel `T(· | x, u)`, bounded reward kernel).

As in the continuous-state file, the conditional expectations `𝔼[· | s[t] = x]` of the sympy `Q_def`, `V_def` are taken
in the regular (kernel) sense; every finite action sum `∑ u, π_θ(u | x) * …` becomes the integral
`∫ u, π_θ(u | x) * … ∂ReferenceMeasure.measure`:

* `rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` (the reward clamped to `[-R, R]`, almost surely equal to it);
* `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]`;
* ;
* ;
* `P1kd θ p x y = ℙ(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p x u y du`, the density (w.r.t. the reference measure
  of `S`) of the next state when `p x u` is the density of `M.env.trans (x, u)`.

The trajectory law `M.traj θ` / `M θ` is the Ionescu–Tulcea measure of the stage chain on `ℕ → ℝ × S × A`,
built like `Model.traj` but with `DensityPolicy.kernel` (`Kernel.withDensity` of the reference measure of `A`)
instead of `Policy.kernel` (`Kernel.ofFunOfCountable`).

These are the continuous-action counterparts of `Model.rk`, `Model.Wk`, `Model.Vk`, `Model.Qk`, `Model.P1k`
(`Def.Dynamics.PolicyTrajectory.Continuous`); the model is time-homogeneous, so none of them depends on `t`.
-/


namespace PolicyGradient

namespace DensityModel

variable {Θ S A : Type*} [MeasurableSpace S] [ReferenceMeasure A]

/-- `rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]`, the expected reward clamped to `[-R, R]` -/
noncomputable def rkd (M : DensityModel Θ S A) (x : S) (u : A) : ℝ :=
  ∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (x, u))

/-- `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]` with a density policy: one policy step (an integral over the actions) and one
transition per `k` -/
noncomputable def Wkd (M : DensityModel Θ S A) (θ : Θ) : ℕ → S → ℝ
  | 0 => fun x => ∫ u, M.policy.prob θ x u * M.rkd x u ∂ReferenceMeasure.measure
  | k + 1 => fun x => ∫ u, M.policy.prob θ x u * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure

/-- state value with a density policy: -/
noncomputable def Vkd (M : DensityModel Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  ∑' k, γ ^ k * M.Wkd θ k x

/-- action value with a density policy:
-/
noncomputable def Qkd (M : DensityModel Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  M.rkd x u + γ * ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u))

/-- `P1kd θ p x y = ℙ(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p(y | x, u) du`, the next-state density
when `p x u` is a density of the transition `M.env.trans (x, u)` -/
noncomputable def P1kd (M : DensityModel Θ S A) (θ : Θ) (p : S → A → S → ℝ) (x y : S) : ℝ :=
  ∫ u, M.policy.prob θ x u * p x u y ∂ReferenceMeasure.measure

variable (M : DensityModel Θ S A)

/-- law of one stage `(r, s, a)` given its state `s`: sample `(s, a, r)` via
`a ∼ π_θ(· | s)`, `r ∼ M.env.reward (s, a)`, then reorder to `(r, s, a)` -/
noncomputable def stageK (θ : Θ) : Kernel S (ℝ × S × A) :=
  (Kernel.deterministic id measurable_id ×ₖ (M.policy.kernel θ ⊗ₖ M.env.reward)).map
    (fun z : S × A × ℝ ↦ (z.2.2, z.1, z.2.1))

end DensityModel
end PolicyGradient
