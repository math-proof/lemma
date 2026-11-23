module

public import Structure.Dynamics.MarkovDecisionProcess
public import Class.Dynamics.MarkovDecisionProcess
public import Class.Probability.Rv
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Instance.Data.Vector.Basic.Dot
public import Instance.Probability.SymbolicProbability
public import Syntax.Probability.Expectation.Elab
public import Def.Order.Miscellaneous

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-!
# Closed-form value functions of the policy-gradient model with continuous states and continuous actions

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`).

The retired finite-action closed forms treated a general (e.g. continuous) state space with a finite action
space (`π_θ(· | x)` was a probability vector on a `[Fintype 𝒜]`).  Here the action space is a general
measurable space with a σ-finite reference measure `ReferenceMeasure.measure` (e.g. Lebesgue measure on `ℝ^m`),
and the policy `π_θ(u | x)` is a probability density of the action w.r.t. it (the `Policy` structure); the environment is the
same `StochasticMDP 𝒮 𝒜` (transition kernel `T(· | x, u)`, bounded reward kernel).

The conditional expectations `𝔼[· | s[t] = x]` of the sympy `Q_def`, `V_def` are taken
in the regular (kernel) sense; every finite action sum `∑ u, π_θ(u | x) * …` becomes the integral
`∫ u, π_θ(u | x) * … ∂ReferenceMeasure.measure`:

* `rkd x u = 𝔼[r[t] | s[t] = x, a[t] = u]` (the reward clamped to `[-R, R]`, almost surely equal to it);
* `Wkd θ k x = 𝔼[r[t+k] | s[t] = x]`;
* `V0 θ γ x = ∑' k, γ ^ k * Wkd θ k x` and `V θ γ t s_t = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s_t)`;
* `Q θ γ t x u = 𝔼[(γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x ∧ a t = u]` and `Q0 θ γ x u = Q θ γ 0 x u`;
* `P1kd θ p x y = ℙ(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p x u y du`, the density (w.r.t. the reference measure
  of `𝒮`) of the next state when `p x u` is the density of `M.trans (x, u)`.

The trajectory law `M.traj θ` / `M θ` is the Ionescu–Tulcea measure of the stage chain on `ℕ → ℝ × 𝒮 × 𝒜`,
built like `Model.traj` but with `Policy.kernel` (`Kernel.withDensity` of the reference measure of `𝒜`)
instead of the retired finite-action kernel (`Kernel.ofFunOfCountable`).

Finite-action discrete policies are the special case of this API with counting measure:
The model is time-homogeneous, so none of the closed forms depends on `t`.
-/

namespace PolicyGradient

namespace Policy

variable {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]

/-- ENNReal density of `π_θ(· | x)` w.r.t. the reference measure of `𝒜` -/
noncomputable def pdf (p : Policy Θ 𝒮 𝒜) (θ : Θ) : 𝒮 → 𝒜 → ENNReal :=
  fun sₜ aₜ => ENNReal.ofReal (p.π[θ] sₜ aₜ)

/-- the action law `π_θ(· | x)` as a Markov kernel `𝒮 → 𝒜` (density w.r.t. `ReferenceMeasure.measure`) -/
noncomputable def kernel (p : Policy Θ 𝒮 𝒜) (θ : Θ) : Kernel 𝒮 𝒜 :=
  Kernel.withDensity (Kernel.const 𝒮 ReferenceMeasure.measure) (p.pdf θ)

theorem measurable_pdf (p : Policy Θ 𝒮 𝒜) [hp : StochasticPolicy p] (θ : Θ) :
    Measurable (Function.uncurry (p.pdf θ)) :=
  show Measurable fun z : 𝒮 × 𝒜 => ENNReal.ofReal (p.π[θ] z.1 z.2) from
    ENNReal.measurable_ofReal.comp (hp.measurable_π θ)

instance (p : Policy Θ 𝒮 𝒜) [hp : StochasticPolicy p] (θ : Θ) : IsMarkovKernel (p.kernel θ) := by
  refine ⟨fun sₜ => ⟨?_⟩⟩
  have hmeas : Measurable (Function.uncurry (p.pdf θ)) := p.measurable_pdf θ
  rw [kernel, Kernel.withDensity_apply _ hmeas, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hnn : 0 ≤ᵐ[ReferenceMeasure.measure] (p.π[θ] sₜ) :=
    Filter.Eventually.of_forall fun aₜ => hp.nonneg θ sₜ aₜ
  have h1 := hp.integral_eq_one θ sₜ
  have hint : Integrable (p.π[θ] sₜ) ReferenceMeasure.measure :=
    integrable_of_integral_eq_one h1
  have : ∫⁻ aₜ, p.pdf θ sₜ aₜ ∂ReferenceMeasure.measure = 1 := by
    simp only [pdf]
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    rw [show ∫ x, p.π[θ] sₜ x ∂ReferenceMeasure.measure = 1 from h1,
      ENNReal.ofReal_one]
  simp [this]

end Policy

namespace Model

variable {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]

/-- `rkd` (reward kernel density): `rkd sₜ aₜ = 𝔼[r[t] | s[t] = sₜ, a[t] = aₜ]`, the expected reward clamped to `[-R, R]` -/
noncomputable def rkd (M : Model Θ 𝒮 𝒜) (R : ℝ) (sₜ : 𝒮) (aₜ : 𝒜) : ℝ :=
  ∫ r_t, clip r_t (-R) R ∂(M.reward (sₜ, aₜ))

/-- `Wkd θ k sₜ = 𝔼[r[t+k] | s[t] = sₜ]` with a density policy: one policy step (an integral over the actions) and one
transition per `k` -/
noncomputable def Wkd (M : Model Θ 𝒮 𝒜) (R : ℝ) (θ : Θ) : ℕ → 𝒮 → ℝ
  | 0 => fun sₜ => ∫ aₜ, M.π[θ] sₜ aₜ * M.rkd R sₜ aₜ ∂ReferenceMeasure.measure
  | k + 1 => fun sₜ => ∫ aₜ, M.π[θ] sₜ aₜ * ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, aₜ)) ∂ReferenceMeasure.measure

/-- `P1kd θ p sₜ y = ℙ(s[t+1] = y | s[t] = sₜ) = ∫ aₜ, π_θ(aₜ | sₜ) * p(y | sₜ, aₜ) daₜ`, the next-state density
when `p sₜ aₜ` is a density of the transition `M.trans (sₜ, aₜ)` -/
noncomputable def P1kd (M : Model Θ 𝒮 𝒜) (θ : Θ) (p : 𝒮 → 𝒜 → 𝒮 → ℝ) (sₜ y : 𝒮) : ℝ :=
  ∫ aₜ, M.π[θ] sₜ aₜ * p sₜ aₜ y ∂ReferenceMeasure.measure

/-- Measurability of `M.trans` and `M.reward` as measure-valued maps.
`StochasticMDP` stores these as `ProbabilityMeasure`-valued functions and does not record
the measurability needed to view them as kernels. -/
class HasMeasurableEnv (M : Model Θ 𝒮 𝒜) : Prop where
  measurable_trans : Measurable (fun p : 𝒮 × 𝒜 => (M.trans p : Measure 𝒮))
  measurable_reward : Measurable (fun p : 𝒮 × 𝒜 => (M.reward p : Measure ℝ))

variable (M : Model Θ 𝒮 𝒜)

/-- Transition kernel associated with `M.trans`. -/
noncomputable def transK [HasMeasurableEnv M] : Kernel (𝒮 × 𝒜) 𝒮 :=
  Kernel.mk (fun p => (M.trans p : Measure 𝒮)) HasMeasurableEnv.measurable_trans

instance instIsMarkovKernel_transK [HasMeasurableEnv M] : IsMarkovKernel M.transK where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (M.trans p : Measure 𝒮)
    infer_instance

/-- Reward kernel associated with `M.reward`. -/
noncomputable def rewardK [HasMeasurableEnv M] : Kernel (𝒮 × 𝒜) ℝ :=
  Kernel.mk (fun p => (M.reward p : Measure ℝ)) HasMeasurableEnv.measurable_reward

instance instIsMarkovKernel_rewardK [HasMeasurableEnv M] : IsMarkovKernel M.rewardK where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (M.reward p : Measure ℝ)
    infer_instance

section MeasurableEnv
variable [HasMeasurableEnv M] [StochasticPolicy M.toPolicy]

/-- law of one stage `(r, s, a)` given its state `s`: sample `(s, a, r)` via
`a ∼ π_θ(· | s)`, `r ∼ M.reward (s, a)`, then reorder to `(r, s, a)` -/
noncomputable def stageK (θ : Θ) : Kernel 𝒮 (ℝ × 𝒮 × 𝒜) :=
  (Kernel.deterministic id measurable_id ×ₖ (M.kernel θ ⊗ₖ M.rewardK)).map
    (fun z : 𝒮 × 𝒜 × ℝ ↦ (z.2.2, z.1, z.2.1))

instance (θ : Θ) : IsMarkovKernel (M.stageK θ) := by
  unfold stageK; exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- transition kernel of the stage chain: `(r, s, a) ↦` law of the next stage -/
noncomputable def K (θ : Θ) : Kernel (ℝ × 𝒮 × 𝒜) (ℝ × 𝒮 × 𝒜) :=
  M.stageK θ ∘ₖ M.transK.comap (fun z ↦ z.2) (by fun_prop)

instance (θ : Θ) : IsMarkovKernel (M.K θ) := by
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
initial stage law is `M.stageK θ ∘ₘ M.init` -/
noncomputable def traj (θ : Θ) : Measure (ℕ → ℝ × 𝒮 × 𝒜) :=
  Kernel.trajMeasure (X := fun _ ↦ ℝ × 𝒮 × 𝒜) (M.stageK θ ∘ₘ (M.init : Measure _)) (M.step θ)

instance (θ : Θ) : IsProbabilityMeasure (M.traj θ) := by
  have : IsProbabilityMeasure (M.init : Measure 𝒮) := inferInstance
  unfold traj; infer_instance

/-- `M[sₜ]` is the action law `θ ↦ π_θ(· | sₜ)`, so `M[sₜ] θ` is `M.kernel θ sₜ`. -/
@[reducible] noncomputable instance instGetElem :
    GetElem (Model Θ 𝒮 𝒜) 𝒮 (Θ → Measure 𝒜) (fun _ _ => True) where
  getElem M sₜ _ := fun θ => M.kernel θ sₜ

theorem getElem_apply (M : Model Θ 𝒮 𝒜) (sₜ : 𝒮) (θ : Θ) :
    M[sₜ] θ = M.kernel θ sₜ :=
  rfl

instance instGetElemIsProbabilityMeasure (M : Model Θ 𝒮 𝒜) [StochasticPolicy M.toPolicy] (sₜ : 𝒮) (θ : Θ) :
    IsProbabilityMeasure (M[sₜ] θ) :=
  inferInstanceAs (IsProbabilityMeasure (M.kernel θ sₜ))

/-- Time-homogeneous state-value as the discounted `Wkd` series, defined on all states:
`V0 θ γ sₜ = ∑' k, γ ^ k * Wkd θ k sₜ`.
Agrees with the conditional expectation `𝔼[(γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[0:] | s 0 = sₜ]` whenever
`ℙ(s[0] = sₜ) ≠ 0`. -/
noncomputable def V0 (M : Model Θ 𝒮 𝒜) (R : ℝ) (θ : Θ) (γ : ℝ) (sₜ : 𝒮) : ℝ :=
  ∑' k, γ ^ k * M.Wkd R θ k sₜ

/-- State-value function:
`V θ γ t sₜ = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = sₜ)`,
where `(r t ω, s t ω, a t ω) = ω t` on the trajectory space. -/
noncomputable def V (M : Model Θ 𝒮 𝒜) [HasMeasurableEnv M] [StochasticPolicy M.toPolicy] (θ : Θ) (γ : ℝ) (t : ℕ) (sₜ : 𝒮) : ℝ :=
  let r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω => (ω t).2.1
  𝔼[r : M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = sₜ)

/-- Action-value function:
`Q θ γ t sₜ aₜ = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = sₜ ∧ a t = aₜ)`,
where `(r t ω, s t ω, a t ω) = ω t` on the trajectory space. -/
noncomputable def Q (M : Model Θ 𝒮 𝒜) [HasMeasurableEnv M] [StochasticPolicy M.toPolicy] (θ : Θ) (γ : ℝ) (t : ℕ) (sₜ : 𝒮) (aₜ : 𝒜) : ℝ :=
  let r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω => (ω t).2.1
  let a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω => (ω t).2.2
  𝔼[r : M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = sₜ ∧ a t = aₜ)

/-- Time-free closed form of the action-value function: `Q0 θ γ sₜ aₜ = Q θ γ 0 sₜ aₜ`. -/
noncomputable def Q0 (M : Model Θ 𝒮 𝒜) [HasMeasurableEnv M] [StochasticPolicy M.toPolicy] (θ : Θ) (γ : ℝ) (sₜ : 𝒮) (aₜ : 𝒜) : ℝ :=
  M.Q θ γ 0 sₜ aₜ

end MeasurableEnv

/-- Infoview: print `Model.traj M θ` (also when written `M.traj θ`) as `M θ`. -/
@[app_unexpander Model.traj]
meta def traj.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M $θ) => `($M $θ)
  | _ => throw ()

end Model
end PolicyGradient
