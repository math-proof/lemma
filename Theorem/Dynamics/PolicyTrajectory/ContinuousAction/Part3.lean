import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Dynamics.PolicyTrajectory.ContinuousAction.Part2
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

variable {M : DensityModel Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}

/-- Under `[IsPolicyTrajectory]` and `[AbsContStateMarginal]`, `s t` is a `SinglePSpace` RV. -/
theorem DensityModel.IsPolicyTrajectory.singlePSpace_s
    [h : DensityModel.IsPolicyTrajectory M r s a]
    [hac : DensityModel.AbsContStateMarginal M s] (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (s t) := by
  have hx : AEMeasurable (s t) (M θ) := (h.measurable_s t).aemeasurable
  let ρ : S → ENNReal := ((M θ).map (s t)).rnDeriv ReferenceMeasure.measure
  refine {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨ρ, ⟨Measure.measurable_rnDeriv _ _⟩, ?_⟩
  }
  exact (Measure.withDensity_rnDeriv_eq _ _ (hac.map_s_ac θ t)).symm

/-- Under `[IsPolicyTrajectory]` and `[AbsContJointAS]`, `(a t, s t)` is a `SinglePSpace` RV. -/
theorem DensityModel.IsPolicyTrajectory.singlePSpace_as
    [h : DensityModel.IsPolicyTrajectory M r s a]
    [haj : DensityModel.AbsContJointAS M a s] (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (a t, s t) := by
  have hxy : AEMeasurable (a t, s t) (M θ) :=
    (h.measurable_a t).aemeasurable.prodMk (h.measurable_s t).aemeasurable
  have hacc : (M θ).map (a t, s t) ≪
      ((ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S)) := by
    change (M θ).map (fun ω => (a t ω, s t ω)) ≪ _
    exact haj.map_as_ac θ t
  exact Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable hxy
    (Measure.measurable_rnDeriv _ _)
    (Measure.withDensity_rnDeriv_eq _ _ hacc).symm

-- `r` is often absent from the conclusion, so these are scoped (HMM / discrete Model pattern):
-- after `open DensityModel.IsPolicyTrajectory`, Lean finds `h` from the local
-- `[IsPolicyTrajectory …]` / `[AbsCont…]` binders.
-- `singlePSpace_as` supplies `(a t, s t)` for `ℙ[M θ](a[t] | s[t])`.

end DensityModelIsPolicyTrajectorySinglePSpace
end PolicyGradient
