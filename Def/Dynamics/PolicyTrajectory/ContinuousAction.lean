import Theorem.Dynamics.PolicyTrajectory
import Class.Probability.Rv.Part3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Structure.Dynamics.PolicyTrajectory.ContinuousAction
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

namespace DensityPolicy

variable {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]

/-- ENNReal density of `π_θ(· | x)` w.r.t. the reference measure of `𝒜` -/
noncomputable def dens (p : DensityPolicy Θ 𝒮 𝒜) (θ : Θ) : 𝒮 → 𝒜 → ENNReal :=
  fun x u => ENNReal.ofReal (p.prob θ x u)

/-- the action law `π_θ(· | x)` as a Markov kernel `𝒮 → 𝒜` (density w.r.t. `ReferenceMeasure.measure`) -/
noncomputable def kernel (p : DensityPolicy Θ 𝒮 𝒜) (θ : Θ) : Kernel 𝒮 𝒜 :=
  Kernel.withDensity (Kernel.const 𝒮 (ReferenceMeasure.measure : Measure 𝒜)) (p.dens θ)

theorem measurable_dens (p : DensityPolicy Θ 𝒮 𝒜) (θ : Θ) :
    Measurable (Function.uncurry (p.dens θ)) :=
  show Measurable fun z : 𝒮 × 𝒜 => ENNReal.ofReal (p.prob θ z.1 z.2) from
    ENNReal.measurable_ofReal.comp (p.measurable_prob θ)

instance (p : DensityPolicy Θ 𝒮 𝒜) (θ : Θ) : IsMarkovKernel (p.kernel θ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have hmeas : Measurable (Function.uncurry (p.dens θ)) := p.measurable_dens θ
  rw [kernel, Kernel.withDensity_apply _ hmeas, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hnn : 0 ≤ᵐ[(ReferenceMeasure.measure : Measure 𝒜)] (p.prob θ x) :=
    Filter.Eventually.of_forall fun u => p.nonneg θ x u
  have h1 := p.integral_eq_one θ x
  have hint : Integrable (p.prob θ x) (ReferenceMeasure.measure : Measure 𝒜) :=
    integrable_of_integral_eq_one h1
  have : ∫⁻ u, p.dens θ x u ∂ReferenceMeasure.measure = 1 := by
    simp only [dens]
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, h1, ENNReal.ofReal_one]
  simp [this]

end DensityPolicy

namespace Policy

variable {Θ 𝒮 𝒜 : Type*}
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]

/-- View a finite-action probability-vector policy as a `DensityPolicy` w.r.t. counting measure.
`sum_eq_one` becomes `integral_eq_one` against `Measure.count`. -/
noncomputable def toDensityPolicy (p : Policy Θ 𝒮 𝒜) : DensityPolicy Θ 𝒮 𝒜 where
  prob := p.prob
  nonneg := p.nonneg
  integral_eq_one := fun θ x => by
    simpa [CountableMeasure.measure_eq_count, MeasureTheory.integral_count] using p.sum_eq_one θ x
  measurable_prob := fun _ => Measurable.of_discrete

end Policy

namespace Model

variable {Θ 𝒮 𝒜 : Type*}
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]

/-- View a discrete finite-action `Model` as a `DensityModel` with action reference `Measure.count`.
Shares `DensityModel.V0` / `Wkd` / `traj` and `DensityModel.IsConditionalProbability`. -/
noncomputable def toDensityModel (M : Model Θ 𝒮 𝒜) : DensityModel Θ 𝒮 𝒜 where
  env := M.env
  policy := M.policy.toDensityPolicy

end Model

namespace DensityModel

variable {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]

/-- `rkd` (reward kernel density): `rkd s_t a_t = 𝔼[r[t] | s[t] = s_t, a[t] = a_t]`, the expected reward clamped to `[-R, R]` -/
noncomputable def rkd (M : DensityModel Θ 𝒮 𝒜) (s_t : 𝒮) (a_t : 𝒜) : ℝ :=
  ∫ r_t, clip r_t (-M.env.R) M.env.R ∂(M.env.reward (s_t, a_t))

/-- `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]` with a density policy: one policy step (an integral over the actions) and one
transition per `k` -/
noncomputable def Wkd (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) : ℕ → 𝒮 → ℝ
  | 0 => fun x => ∫ u, M.policy.prob θ x u * M.rkd x u ∂ReferenceMeasure.measure
  | k + 1 => fun x => ∫ u, M.policy.prob θ x u * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure

/-- `P1kd θ p x y = ℙ(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p(y | x, u) du`, the next-state density
when `p x u` is a density of the transition `M.env.trans (x, u)` -/
noncomputable def P1kd (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (p : 𝒮 → 𝒜 → 𝒮 → ℝ) (x y : 𝒮) : ℝ :=
  ∫ u, M.policy.prob θ x u * p x u y ∂ReferenceMeasure.measure

variable (M : DensityModel Θ 𝒮 𝒜)

/-- law of one stage `(r, s, a)` given its state `s`: sample `(s, a, r)` via
`a ∼ π_θ(· | s)`, `r ∼ M.env.reward (s, a)`, then reorder to `(r, s, a)` -/
noncomputable def stageK (θ : Θ) : Kernel 𝒮 (ℝ × 𝒮 × 𝒜) :=
  (Kernel.deterministic id measurable_id ×ₖ (M.policy.kernel θ ⊗ₖ M.env.reward)).map
    (fun z : 𝒮 × 𝒜 × ℝ ↦ (z.2.2, z.1, z.2.1))

instance (θ : Θ) : IsMarkovKernel (M.stageK θ) := by
  have := M.env.reward_markov
  unfold stageK; exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- transition kernel of the stage chain: `(r, s, a) ↦` law of the next stage -/
noncomputable def K (θ : Θ) : Kernel (ℝ × 𝒮 × 𝒜) (ℝ × 𝒮 × 𝒜) :=
  M.stageK θ ∘ₖ M.env.trans.comap (fun z ↦ z.2) (by fun_prop)

instance (θ : Θ) : IsMarkovKernel (M.K θ) := by
  have := M.env.trans_markov
  unfold K; infer_instance

/-- `j`-step kernel expectation of `f` along the stage chain: `z ↦ 𝔼[f (ω (t + j)) | ω t = z]` -/
noncomputable def Kf (θ : Θ) (f : ℝ × 𝒮 × 𝒜 → ℝ) : ℕ → ℝ × 𝒮 × 𝒜 → ℝ
  | 0 => f
  | j + 1 => fun z ↦
    let w : ℝ × 𝒮 × 𝒜 → ℝ × 𝒮 × 𝒜 := id
    have : PSpace (M.K θ z) w := { aemeasurable := measurable_id.aemeasurable }
    𝔼[w : M.K θ z](Kf θ f j w)

/-- the stage chain seen as history-dependent kernels (only the last stage matters) -/
noncomputable def step (θ : Θ) (n : ℕ) : Kernel (Π _ : Finset.Iic n, ℝ × 𝒮 × 𝒜) (ℝ × 𝒮 × 𝒜) :=
  (M.K θ).comap (fun h ↦ h ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (θ : Θ) (n : ℕ) : IsMarkovKernel (M.step θ n) := by
  unfold step; infer_instance

/-- law of the whole trajectory under the weights `θ` (Ionescu-Tulcea);
initial stage law is `M.stageK θ ∘ₘ M.env.init` -/
noncomputable def traj (θ : Θ) : Measure (ℕ → ℝ × 𝒮 × 𝒜) :=
  Kernel.trajMeasure (X := fun _ ↦ ℝ × 𝒮 × 𝒜) (M.stageK θ ∘ₘ M.env.init) (M.step θ)

instance (θ : Θ) : IsProbabilityMeasure (M.traj θ) := by
  have := M.env.init_prob
  unfold traj; infer_instance

/-- `M θ` is the trajectory law `M.traj θ`. -/
noncomputable instance instCoeFun : CoeFun (DensityModel Θ 𝒮 𝒜) (fun _ ↦ Θ → Measure (ℕ → ℝ × 𝒮 × 𝒜)) where
  coe M := M.traj

/-- `M[x]` is the action law `θ ↦ π_θ(· | x)`, so `M[x] θ` is `M.policy.kernel θ x`. -/
@[reducible] noncomputable instance instGetElem :
    GetElem (DensityModel Θ 𝒮 𝒜) 𝒮 (Θ → Measure 𝒜) (fun _ _ => True) where
  getElem M x _ := fun θ => M.policy.kernel θ x

theorem getElem_apply (M : DensityModel Θ 𝒮 𝒜) (x : 𝒮) (θ : Θ) :
    M[x] θ = M.policy.kernel θ x :=
  rfl

instance instGetElemIsProbabilityMeasure (M : DensityModel Θ 𝒮 𝒜) (x : 𝒮) (θ : Θ) :
    IsProbabilityMeasure (M[x] θ) :=
  inferInstanceAs (IsProbabilityMeasure (M.policy.kernel θ x))

/-- Time-homogeneous state-value as the discounted `Wkd` series, defined on all states:
`V0 θ γ x = ∑' k, γ ^ k * Wkd θ k x`.
Agrees with the conditional expectation `𝔼[(γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[0:] | s 0 = x]` whenever
`ℙ(s[0] = x) ≠ 0`. -/
noncomputable def V0 (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (γ : ℝ) (x : 𝒮) : ℝ :=
  ∑' k, γ ^ k * M.Wkd θ k x

/-- State-value function:
`V θ γ t s_t = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s_t)`,
where `(r t ω, s t ω, a t ω) = ω t` on the trajectory space. -/
noncomputable def V (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (γ : ℝ) (t : ℕ) (s_t : 𝒮) : ℝ :=
  let r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω => (ω t).2.1
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s_t)

/-- Action-value function:
`Q θ γ t s_t a_t = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s_t ∧ a t = a_t)`,
where `(r t ω, s t ω, a t ω) = ω t` on the trajectory space. -/
noncomputable def Q (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (γ : ℝ) (t : ℕ) (s_t : 𝒮) (a_t : 𝒜) : ℝ :=
  let r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω => (ω t).2.1
  let a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω => (ω t).2.2
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s_t ∧ a t = a_t)

/-- Time-free closed form of the action-value function: `Q0 θ γ x u = Q θ γ 0 x u`. -/
noncomputable def Q0 (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (γ : ℝ) (x : 𝒮) (u : 𝒜) : ℝ :=
  M.Q θ γ 0 x u

/-- Infoview: print `DensityModel.traj M θ` (also when written `M.traj θ`) as `M θ`. -/
@[app_unexpander DensityModel.traj]
def traj.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M $θ) => `($M $θ)
  | _ => throw ()

set_option linter.unusedVariables false in
/-- State coordinate at time `t` on a trajectory `ω : ℕ → ℝ × 𝒮 × 𝒜`
(`ω t = (r t, s t, a t)`). Dot notation: `M.stateAt t`. -/
def stateAt (M : DensityModel Θ 𝒮 𝒜) (t : ℕ) : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 :=
  fun ω ↦ (ω t).2.1

set_option linter.unusedVariables false in
/-- Action coordinate at time `t` on a trajectory. Dot notation: `M.actionAt t`. -/
def actionAt (M : DensityModel Θ 𝒮 𝒜) (t : ℕ) : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 :=
  fun ω ↦ (ω t).2.2

set_option linter.unusedVariables false in
/-- Reward coordinate at time `t` on a trajectory. Dot notation: `M.rewardAt t`. -/
def rewardAt (M : DensityModel Θ 𝒮 𝒜) (t : ℕ) : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ :=
  fun ω ↦ (ω t).1

end DensityModel
end PolicyGradient
