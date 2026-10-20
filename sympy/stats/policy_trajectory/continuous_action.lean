import sympy.stats.policy_trajectory
import sympy.stats.rv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import sympy.functions.elementary.miscellaneous

/-!
# Closed-form value functions of the policy-gradient model with continuous states and continuous actions

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`).

`sympy.stats.policy_trajectory.continuous` treats a general (e.g. continuous) state space with a finite action
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
* `P1kd θ p x y = Pr(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p x u y du`, the density (w.r.t. the reference measure
  of `S`) of the next state when `p x u` is the density of `M.env.trans (x, u)`.

The trajectory law `M.traj θ` / `M θ` is the Ionescu–Tulcea measure of the stage chain on `ℕ → ℝ × S × A`,
built like `Model.traj` but with `DensityPolicy.kernel` (`Kernel.withDensity` of the reference measure of `A`)
instead of `Policy.kernel` (`Kernel.ofFunOfCountable`).

These are the continuous-action counterparts of `Model.rk`, `Model.Wk`, `Model.Vk`, `Model.Qk`, `Model.P1k`
(`sympy.stats.policy_trajectory.continuous`); the model is time-homogeneous, so none of them depends on `t`.
-/
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace PolicyGradient

/-- A stochastic policy on a general (e.g. continuous) action space: `prob θ x u = π_θ(u | x)` is a probability density
of the action `a[t]` given the state `s[t] = x` w.r.t. the reference measure of `A`
(continuous-action counterpart of `Policy`, whose `sum_eq_one` becomes `integral_eq_one`). -/
structure DensityPolicy (Θ S A : Type*) [MeasurableSpace S] [ReferenceMeasure A] where
  prob : Θ → S → A → ℝ
  nonneg : ∀ θ x u, 0 ≤ prob θ x u
  integral_eq_one : ∀ θ x, ∫ u, prob θ x u ∂(ReferenceMeasure.measure : Measure A) = 1
  measurable_prob : ∀ θ, Measurable (fun z : S × A => prob θ z.1 z.2)

namespace DensityPolicy

variable {Θ S A : Type*} [MeasurableSpace S] [ReferenceMeasure A]

/-- ENNReal density of `π_θ(· | x)` w.r.t. the reference measure of `A` -/
noncomputable def dens (p : DensityPolicy Θ S A) (θ : Θ) : S → A → ℝ≥0∞ :=
  fun x u => ENNReal.ofReal (p.prob θ x u)

/-- the action law `π_θ(· | x)` as a Markov kernel `S → A` (density w.r.t. `ReferenceMeasure.measure`) -/
noncomputable def kernel (p : DensityPolicy Θ S A) (θ : Θ) : Kernel S A :=
  Kernel.withDensity (Kernel.const S (ReferenceMeasure.measure : Measure A)) (p.dens θ)

theorem measurable_dens (p : DensityPolicy Θ S A) (θ : Θ) :
    Measurable (Function.uncurry (p.dens θ)) :=
  show Measurable fun z : S × A => ENNReal.ofReal (p.prob θ z.1 z.2) from
    ENNReal.measurable_ofReal.comp (p.measurable_prob θ)

instance (p : DensityPolicy Θ S A) (θ : Θ) : IsMarkovKernel (p.kernel θ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have hmeas : Measurable (Function.uncurry (p.dens θ)) := p.measurable_dens θ
  rw [kernel, Kernel.withDensity_apply _ hmeas, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hnn : 0 ≤ᵐ[(ReferenceMeasure.measure : Measure A)] (p.prob θ x) :=
    Filter.Eventually.of_forall fun u => p.nonneg θ x u
  have h1 := p.integral_eq_one θ x
  have hint : Integrable (p.prob θ x) (ReferenceMeasure.measure : Measure A) :=
    integrable_of_integral_eq_one h1
  have : ∫⁻ u, p.dens θ x u ∂ReferenceMeasure.measure = 1 := by
    simp only [dens]
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, h1, ENNReal.ofReal_one]
  simp [this]

end DensityPolicy

/-- The policy-gradient model with a density policy on a general action space
(continuous-action counterpart of `Model`; the environment `Env S A` is unchanged). -/
structure DensityModel (Θ S A : Type*) [MeasurableSpace S] [ReferenceMeasure A] where
  env : Env S A
  policy : DensityPolicy Θ S A

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

/-- `P1kd θ p x y = Pr(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p(y | x, u) du`, the next-state density
when `p x u` is a density of the transition `M.env.trans (x, u)` -/
noncomputable def P1kd (M : DensityModel Θ S A) (θ : Θ) (p : S → A → S → ℝ) (x y : S) : ℝ :=
  ∫ u, M.policy.prob θ x u * p x u y ∂ReferenceMeasure.measure

variable (M : DensityModel Θ S A)

/-- law of one stage `(r, s, a)` given its state `s`: sample `(s, a, r)` via
`a ∼ π_θ(· | s)`, `r ∼ M.env.reward (s, a)`, then reorder to `(r, s, a)` -/
noncomputable def stageK (θ : Θ) : Kernel S (ℝ × S × A) :=
  (Kernel.deterministic id measurable_id ×ₖ (M.policy.kernel θ ⊗ₖ M.env.reward)).map
    (fun z : S × A × ℝ ↦ (z.2.2, z.1, z.2.1))

instance (θ : Θ) : IsMarkovKernel (M.stageK θ) := by
  have := M.env.reward_markov
  unfold stageK; exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- transition kernel of the stage chain: `(r, s, a) ↦` law of the next stage -/
noncomputable def K (θ : Θ) : Kernel (ℝ × S × A) (ℝ × S × A) :=
  M.stageK θ ∘ₖ M.env.trans.comap (fun z ↦ z.2) (by fun_prop)

instance (θ : Θ) : IsMarkovKernel (M.K θ) := by
  have := M.env.trans_markov
  unfold K; infer_instance

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

instance (θ : Θ) (n : ℕ) : IsMarkovKernel (M.step θ n) := by
  unfold step; infer_instance

/-- law of the whole trajectory under the weights `θ` (Ionescu-Tulcea);
initial stage law is `M.stageK θ ∘ₘ M.env.init` -/
noncomputable def traj (θ : Θ) : Measure (ℕ → ℝ × S × A) :=
  Kernel.trajMeasure (X := fun _ ↦ ℝ × S × A) (M.stageK θ ∘ₘ M.env.init) (M.step θ)

instance (θ : Θ) : IsProbabilityMeasure (M.traj θ) := by
  have := M.env.init_prob
  unfold traj; infer_instance

/-- `M θ` is the trajectory law `M.traj θ` (it elaborates to `DensityModel.traj M θ`). -/
noncomputable instance instCoeFun : CoeFun (DensityModel Θ S A) (fun _ ↦ Θ → Measure (ℕ → ℝ × S × A)) where
  coe M := M.traj

/-- Infoview: print `DensityModel.traj M θ` (also when written `M.traj θ`) as `M θ`. -/
@[app_unexpander DensityModel.traj]
def traj.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M $θ) => `($M $θ)
  | _ => throw ()

end DensityModel

end PolicyGradient
