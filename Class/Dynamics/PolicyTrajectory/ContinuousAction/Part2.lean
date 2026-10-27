import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part2
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

variable {Θ S A : Type*} [MeasurableSpace S] [ReferenceMeasure A]

section DensityModelIsPolicyTrajectorySinglePSpace

variable {Θ S A : Type*} [ReferenceMeasure S] [ReferenceMeasure A]

/-- Absolute continuity of every state marginal `law(s[t])` w.r.t. `ReferenceMeasure` on `S`. -/
class DensityModel.AbsContStateMarginal (M : DensityModel Θ S A)
    (s : ℕ ⇀ (ℕ → ℝ × S × A) → S) : Prop where
  map_s_ac : ∀ θ t, (M θ).map (s t) ≪ (ReferenceMeasure.measure : Measure S)

/-- Absolute continuity of every joint law `law(a[t], s[t])` w.r.t. the product reference
measure on `A × S`. Together with `AbsContStateMarginal`, enables `SinglePSpace` for
`(a t, s t)` so `ℙ[M θ](a[t] | s[t])` elaborates. -/
class DensityModel.AbsContJointAS (M : DensityModel Θ S A)
    (a : ℕ ⇀ (ℕ → ℝ × S × A) → A)
    (s : ℕ ⇀ (ℕ → ℝ × S × A) → S) : Prop where
  map_as_ac : ∀ θ t,
    (M θ).map (fun ω => (a t ω, s t ω)) ≪
      ((ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S))

end DensityModelIsPolicyTrajectorySinglePSpace
end PolicyGradient
