import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Instance.Dynamics.PolicyTrajectory.ContinuousAction.Part5
import Syntax.Probability.Probability
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal ENNReal.ToRealCoe

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

/-- Stage coordinates `(r[t], s[t], a[t])` match the trajectory point `ω t` for every `t`. -/
class DensityModel.IsPolicyTrajectory (M : DensityModel Θ S A)
    (r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ)
    (s : ℕ ⇀ (ℕ → ℝ × S × A) → S)
    (a : ℕ ⇀ (ℕ → ℝ × S × A) → A) : Prop where
  /-- Same as lemma `h₁`: the stage map is the joint `(r t, s t, a t)`. -/
  stage_eq : ∀ t, (· t) = (r t, s t, a t)

namespace DensityModel.IsPolicyTrajectory

variable {M : DensityModel Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}

/-- `s t` is measurable: rewrite via `stage_eq` to `(ω t).2.1`. -/
theorem measurable_s [h : DensityModel.IsPolicyTrajectory M r s a] (t : ℕ) :
    Measurable (s t) := by
  have : s t = fun ω : ℕ → ℝ × S × A ↦ (ω t).2.1 :=
    funext fun ω ↦ (congrArg (fun z : ℝ × S × A ↦ z.2.1) (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_fst.comp <| measurable_snd.comp <|
    (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t)

/-- `a t` is measurable: rewrite via `stage_eq` to `(ω t).2.2`. -/
theorem measurable_a [h : DensityModel.IsPolicyTrajectory M r s a] (t : ℕ) :
    Measurable (a t) := by
  have : a t = fun ω : ℕ → ℝ × S × A ↦ (ω t).2.2 :=
    funext fun ω ↦ (congrArg (fun z : ℝ × S × A ↦ z.2.2) (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_snd.comp <| measurable_snd.comp <|
    (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t)

/-- `r t` is measurable: rewrite via `stage_eq` to `(ω t).1`. -/
theorem measurable_r [h : DensityModel.IsPolicyTrajectory M r s a] (t : ℕ) :
    Measurable (r t) := by
  have : r t = fun ω : ℕ → ℝ × S × A ↦ (ω t).1 :=
    funext fun ω ↦ (congrArg Prod.fst (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_fst.comp (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t)

end DensityModel.IsPolicyTrajectory

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

variable {M : DensityModel Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}

set_option synthInstance.checkSynthOrder false

/-- Under `[IsPolicyTrajectory]` and `[AbsContStateMarginal]`, `s t` is a `SinglePSpace` RV. -/
instance DensityModel.IsPolicyTrajectory.singlePSpace_s
    [h : DensityModel.IsPolicyTrajectory M r s a]
    [hac : DensityModel.AbsContStateMarginal M s] (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (s t) := by
  have hx : AEMeasurable (s t) (M θ) := (h.measurable_s t).aemeasurable
  let ρ : S → ENNReal := ((M θ).map (s t)).rnDeriv ReferenceMeasure.measure
  refine {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨ρ, Measure.measurable_rnDeriv _ _, ?_⟩
  }
  exact (Measure.withDensity_rnDeriv_eq _ _ (hac.map_s_ac θ t)).symm

/-- Under `[IsPolicyTrajectory]` and `[AbsContJointAS]`, `(a t, s t)` is a `SinglePSpace` RV. -/
instance DensityModel.IsPolicyTrajectory.singlePSpace_as
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

/-- Policy density equals the conditional of the trajectory law.
`htr` and `haj` are the stage-coordinate and joint absolute-continuity assumptions
`ℙ[M θ](a[t] | s[t])` needs, packed here so a lemma can take this class alone. -/
class DensityModel.IsConditionalProbability
    (M : DensityModel Θ S A)
    (r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ)
    (s : ℕ ⇀ (ℕ → ℝ × S × A) → S)
    (a : ℕ ⇀ (ℕ → ℝ × S × A) → A) : Prop where
  htr : DensityModel.IsPolicyTrajectory M r s a
  haj : DensityModel.AbsContJointAS M a s
  /-- One stage of the policy density matches the trajectory conditional. -/
  factor : ∀ θ t (x : S) (u : A),
    M.policy.prob θ x u =
      (ℙ[M θ]((a t) = u | (s t) = x) : ℝ)

instance [h : DensityModel.IsConditionalProbability M r s a] :
    DensityModel.IsPolicyTrajectory M r s a :=
  h.htr

instance [h : DensityModel.IsConditionalProbability M r s a] :
    DensityModel.AbsContJointAS M a s :=
  h.haj

end DensityModelIsPolicyTrajectorySinglePSpace
end PolicyGradient
