import sympy.stats.policy_trajectory
import sympy.stats.rv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import sympy.functions.elementary.miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

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
* `P1kd θ p x y = ℙ(s[t+1] = y | s[t] = x) = ∫ u, π_θ(u | x) * p x u y du`, the density (w.r.t. the reference measure
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

set_option linter.unusedVariables false in
/-- State coordinate at time `t` on a trajectory `ω : ℕ → ℝ × S × A`
(`ω t = (r t, s t, a t)`). Dot notation: `M.stateAt t`. -/
def stateAt (M : DensityModel Θ S A) (t : ℕ) : (ℕ → ℝ × S × A) → S :=
  fun ω ↦ (ω t).2.1

set_option linter.unusedVariables false in
/-- Action coordinate at time `t` on a trajectory. Dot notation: `M.actionAt t`. -/
def actionAt (M : DensityModel Θ S A) (t : ℕ) : (ℕ → ℝ × S × A) → A :=
  fun ω ↦ (ω t).2.2

set_option linter.unusedVariables false in
/-- Reward coordinate at time `t` on a trajectory. Dot notation: `M.rewardAt t`. -/
def rewardAt (M : DensityModel Θ S A) (t : ℕ) : (ℕ → ℝ × S × A) → ℝ :=
  fun ω ↦ (ω t).1

end DensityModel

/-! ### `IsPolicyTrajectory` for continuous-action density models

Bundles `stage_eq` (same content as lemma `h₁ : ∀ t, (· t) = (r t, s t, a t)`).
For `ℙ[M θ](a[t] | s[t])` to elaborate one needs `[ReferenceMeasure S]` as well as
`[ReferenceMeasure A]`, plus absolute continuity of the state / joint action-state
marginals w.r.t. the reference measures (not implied by `Env` alone: `init` / `trans`
may be singular w.r.t. `ReferenceMeasure` on `S`). Package those as
`[AbsContStateMarginal M s]` and `[AbsContJointAS M a s]`; scoped `SinglePSpace`
instances under `namespace IsPolicyTrajectory` then mirror the discrete
`CountableMeasure` helpers. The joint abs.continuity follows from the policy density
factorization once `map (s t) ≪ ref_S` (proved in Random lemmas via `stageK`); the
class keeps the hypothesis explicit so `sympy/` stays free of that dependency. -/

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

/-- Canonical projections form an `IsPolicyTrajectory` (`stage_eq` by `rfl`). -/
instance instCanonical (M : DensityModel Θ S A) :
    DensityModel.IsPolicyTrajectory M ⟨M.rewardAt⟩ ⟨M.stateAt⟩ ⟨M.actionAt⟩ where
  stage_eq t := by
    funext ω
    rfl

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

end DensityModelIsPolicyTrajectorySinglePSpace

namespace DensityModel.IsPolicyTrajectory
-- `r` is often absent from the conclusion, so these are scoped (HMM / discrete Model pattern):
-- after `open DensityModel.IsPolicyTrajectory`, Lean finds `h` from the local
-- `[IsPolicyTrajectory …]` / `[AbsCont…]` binders.
-- `singlePSpace_as` supplies `(a t, s t)` for `ℙ[M θ](a[t] | s[t])`.
set_option synthInstance.checkSynthOrder false in
attribute [scoped instance] singlePSpace_s singlePSpace_as
end DensityModel.IsPolicyTrajectory

end PolicyGradient
