module

public import Structure.Dynamics.MarkovDecisionProcess
public import Class.Dynamics.MarkovDecisionProcess
public import Class.Probability.Rv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Probability.Kernel.WithDensity
public import Def.Order.Miscellaneous
public import Theorem.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Instance.Analysis.Real.Numbers
public import Instance.Data.Nat.Fun
public import Def.Dynamics.PolicyTrajectory.ContinuousAction
public import Syntax.Probability.Probability
public section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal ENNReal.ToRealCoe

namespace PolicyGradient

variable {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]

/-- Stage coordinates `(r[t], s[t], a[t])` match the trajectory point `ω t` for every `t`. -/
class Model.IsPolicyTrajectory (M : Model Θ 𝒮 𝒜)
    (r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ)
    (s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮)
    (a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜) : Prop where
  /-- Same as lemma `h₁`: the stage map is the joint `(r t, s t, a t)`. -/
  stage_eq : ∀ t, (· t) = (r t, s t, a t)

namespace Model.IsPolicyTrajectory

variable {M : Model Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}

/-- `s t` is measurable: rewrite via `stage_eq` to `(ω t).2.1`. -/
theorem measurable_s [h : Model.IsPolicyTrajectory M r s a] (t : ℕ) :
    Measurable (s t) := by
  have : s t = fun ω : ℕ → ℝ × 𝒮 × 𝒜 ↦ (ω t).2.1 :=
    funext fun ω ↦ (congrArg (fun z : ℝ × 𝒮 × 𝒜 ↦ z.2.1) (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_fst.comp <| measurable_snd.comp <|
    (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × 𝒮 × 𝒜) t)

/-- `a t` is measurable: rewrite via `stage_eq` to `(ω t).2.2`. -/
theorem measurable_a [h : Model.IsPolicyTrajectory M r s a] (t : ℕ) :
    Measurable (a t) := by
  have : a t = fun ω : ℕ → ℝ × 𝒮 × 𝒜 ↦ (ω t).2.2 :=
    funext fun ω ↦ (congrArg (fun z : ℝ × 𝒮 × 𝒜 ↦ z.2.2) (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_snd.comp <| measurable_snd.comp <|
    (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × 𝒮 × 𝒜) t)

/-- `r t` is measurable: rewrite via `stage_eq` to `(ω t).1`. -/
theorem measurable_r [h : Model.IsPolicyTrajectory M r s a] (t : ℕ) :
    Measurable (r t) := by
  have : r t = fun ω : ℕ → ℝ × 𝒮 × 𝒜 ↦ (ω t).1 :=
    funext fun ω ↦ (congrArg Prod.fst (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_fst.comp (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × 𝒮 × 𝒜) t)

end Model.IsPolicyTrajectory

section ModelIsPolicyTrajectorySinglePSpace

variable {Θ 𝒮 𝒜 : Type*} [ReferenceMeasure 𝒮] [ReferenceMeasure 𝒜]

/-- Absolute continuity of every state marginal `law(s[t])` w.r.t. `ReferenceMeasure` on `𝒮`. -/
class Model.AbsContStateMarginal (M : Model Θ 𝒮 𝒜) [Model.HasMeasurableEnv M] [StochasticPolicy M.toPolicy]
    (s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮) : Prop where
  map_s_ac : ∀ θ t, (M.traj θ).map (s t) ≪ ReferenceMeasure.measure

/-- Absolute continuity of every joint law `law(a[t], s[t])` w.r.t. the product reference
measure on `𝒜 × 𝒮`. Together with `AbsContStateMarginal`, enables `SinglePSpace` for
`(a t, s t)` so `ℙ[M.traj θ](a[t] | s[t])` elaborates. -/
class Model.AbsContJointAS (M : Model Θ 𝒮 𝒜) [Model.HasMeasurableEnv M] [StochasticPolicy M.toPolicy]
    (a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜)
    (s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮) : Prop where
  map_as_ac : ∀ θ t,
    (M.traj θ).map (fun ω => (a t ω, s t ω)) ≪
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure)

variable {M : Model Θ 𝒮 𝒜} [Model.HasMeasurableEnv M] [StochasticPolicy M.toPolicy]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}

set_option synthInstance.checkSynthOrder false

/-- Under `[IsPolicyTrajectory]` and `[AbsContStateMarginal]`, `s t` is a `SinglePSpace` RV. -/
instance Model.IsPolicyTrajectory.singlePSpace_s
    [h : Model.IsPolicyTrajectory M r s a]
    [hac : Model.AbsContStateMarginal M s] (θ : Θ) (t : ℕ) :
    SinglePSpace (M.traj θ) (s t) := by
  have hx : AEMeasurable (s t) (M.traj θ) := (h.measurable_s t).aemeasurable
  let ρ : 𝒮 → ENNReal := ((M.traj θ).map (s t)).rnDeriv ReferenceMeasure.measure
  refine {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨ρ, Measure.measurable_rnDeriv _ _, ?_⟩
  }
  exact (Measure.withDensity_rnDeriv_eq _ _ (hac.map_s_ac θ t)).symm

/-- Under `[IsPolicyTrajectory]` and `[AbsContJointAS]`, `(a t, s t)` is a `SinglePSpace` RV. -/
instance Model.IsPolicyTrajectory.singlePSpace_as
    [h : Model.IsPolicyTrajectory M r s a]
    [haj : Model.AbsContJointAS M a s] (θ : Θ) (t : ℕ) :
    SinglePSpace (M.traj θ) (a t, s t) := by
  have hxy : AEMeasurable (fun ω => (a t ω, s t ω)) (M.traj θ) :=
    (h.measurable_a t).aemeasurable.prodMk (h.measurable_s t).aemeasurable
  have hacc : (M.traj θ).map (fun ω => (a t ω, s t ω)) ≪
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure) :=
    haj.map_as_ac θ t
  exact Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable hxy
    (Measure.measurable_rnDeriv _ _)
    (Measure.withDensity_rnDeriv_eq _ _ hacc).symm

/-- Policy density equals the conditional of the trajectory law.
`htr` and `haj` are the stage-coordinate and joint absolute-continuity assumptions
`ℙ[M.traj θ](a[t] | s[t])` needs, packed here so a lemma can take this class alone. -/
class Model.IsConditionalProbability
    (M : Model Θ 𝒮 𝒜) [Model.HasMeasurableEnv M] [StochasticPolicy M.toPolicy]
    (r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ)
    (s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮)
    (a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜) : Prop where
  htr : Model.IsPolicyTrajectory M r s a
  haj : Model.AbsContJointAS M a s
  /-- One stage of the policy density matches the trajectory conditional. -/
  factor : ∀ θ t (sₜ : 𝒮) (aₜ : 𝒜)
      [SinglePSpace (M.traj θ) (fun ω => (a t ω, s t ω))],
    M.π[θ] sₜ aₜ = ℙ[M.traj θ](a[t] = aₜ | s[t] = sₜ)

instance [h : Model.IsConditionalProbability M r s a] :
    Model.IsPolicyTrajectory M r s a :=
  h.htr

instance [h : Model.IsConditionalProbability M r s a] :
    Model.AbsContJointAS M a s :=
  h.haj

end ModelIsPolicyTrajectorySinglePSpace
end PolicyGradient
