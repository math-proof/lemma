import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Instance.Dynamics.PolicyTrajectory.ContinuousAction.Part3
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

variable (M : DensityModel Θ S A)

/-- `j`-step kernel expectation of `f` along the stage chain: `z ↦ 𝔼[f (ω (t + j)) | ω t = z]` -/
noncomputable def Kf (θ : Θ) (f : ℝ × S × A → ℝ) : ℕ → ℝ × S × A → ℝ
  | 0 => f
  | j + 1 => fun z ↦
    let w : ℝ × S × A → ℝ × S × A := id
    have : PSpace (M.K θ z) w := { aemeasurable := measurable_id.aemeasurable }
    𝔼[w : M.K θ z](Kf θ f j w)

/-- the stage chain seen as history-dependent kernels (only the last stage matters) -/
noncomputable def step (θ : Θ) (n : ℕ) : Kernel (Π _ : Finset.Iic n, ℝ × S × A) (ℝ × S × A) :=
  (M.K θ).comap (fun h ↦ h ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

end DensityModel
end PolicyGradient
