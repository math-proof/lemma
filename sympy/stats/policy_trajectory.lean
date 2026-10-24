import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import sympy.stats.variance
import sympy.core.numbers
import sympy.core.power
import sympy.vector.Basic
import stdlib.List
import sympy.core.function
import Lemma.Random.SinglePSpace.of.Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable

/-!
# Shared trajectory model for the policy-gradient lemmas (standard MDP)

Lean model behind the sympy symbols used in `Tensor.*.policy_gradient_theorem`,
`Tensor.*.unbiased_advantage_estimate` and their dependencies:

* `s : ℕ → Ω → S` (states), `a : ℕ → Ω → A` (actions), `r : ℕ → Ω → ℝ` (rewards),
  with `S` and `A` finite;
* `π` (the trainable weights) is a point `θ` of a real normed space `Θ`;
* `Pr[a:π](a[t] | s[t])` is the policy `M.policy.prob θ (s t) (a t)`;
* `Expectation[r, a:π](f)` is the Bochner integral `∫ ω, f ω ∂(M θ)`;
* `Expectation[...](f | s[t] = x)` is the integral against Mathlib's conditional measure
  `(M θ)[| s t ⁻¹' {x}]`;
* / `(γ ^ (id : ℕ → ℕ)) @ r[t:]` is `∑' k, γ ^ k * r (t + k)`;
* `Derivative[π]` is `fderiv ℝ · θ`.

The environment is a standard (time-homogeneous) MDP: `s 0 ∼ init`, `a t ∼ π_θ(· | s t)`,
`r t ∼ M.env.reward (s t, a t)`, `s (t + 1) ∼ trans (s t, a t)`, rewards bounded by `R`.
The stage process `ω t = (r t ω, s t ω, a t ω)` (reward first, then the state-action pair, the order of the
joint random variable `(r t, s t, a t)`) is a time-homogeneous Markov chain on `ℝ × S × A` with kernel
`M.K θ`; its law `M.traj θ` is Mathlib's Ionescu-Tulcea measure `Kernel.trajMeasure` on `ℕ → ℝ × S × A`.
Canonical path projections `M.stateAt t`, `M.actionAt t`, `M.rewardAt t` extract the coordinates of
`ω t = (r t ω, s t ω, a t ω)` (internal helpers; under `[CountableMeasure S]` / `[CountableMeasure A]`
they also carry `SinglePSpace`). For **public** Random lemmas prefer the HMM-style class
`IsPolicyTrajectory M r s a` (`stage_eq` = today's `h₁`) so hyps can use `s[0]` /
`(ℙ[M θ](s[0] = x) : ℝ) ≠ 0` with no `hPs0` and no public `M.stateAt 0`. Lemmas may still bind
`{r s a}` with `h₁ : ∀ t, (· t) = (r t, s t, a t)` (the joint random variable of
`Function.coeProdPi3R`), or take `[IsPolicyTrajectory M r s a]` instead. State / action values are introduced locally in lemmas as
`V`: `𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)` and
`Q`: `𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)`.
Clamped rewards are local `rc z := clip z.1 (-M.env.R) M.env.R` (a.s. equal to the raw reward).
The j-step stage map is local
`W θ f j y := 𝔼[z : M.stageK θ y](M.Kf θ f j z)` (identity RV + `PSpace` on `M.stageK θ y`).
The reward `r t` belongs to stage `t`: `r t ∼ M.env.reward (s t, a t)`.  The sympy reward hypothesis `Equal(r[t] | s[:t] & a[:t], r[t])` is not
built in; lemmas that carry it in sympy keep it as an explicit named hypothesis.
-/
open MeasureTheory ProbabilityTheory Finset

namespace PolicyGradient

/-- a stochastic policy `π_θ(a | s)` on a finite action space, parametrised by `θ : Θ` -/
structure Policy (Θ S A : Type*) [Fintype A] where
  prob : Θ → S → A → ℝ
  nonneg : ∀ θ x a, 0 ≤ prob θ x a
  sum_eq_one : ∀ θ x, ∑ a, prob θ x a = 1

/-- standard MDP environment on a finite state space with bounded rewards -/
structure Env (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  init : Measure S
  init_prob : IsProbabilityMeasure init
  trans : Kernel (S × A) S
  trans_markov : IsMarkovKernel trans
  reward : Kernel (S × A) ℝ
  reward_markov : IsMarkovKernel reward
  R : ℝ
  reward_bdd : ∀ p, reward p (Set.Icc (-R) R)ᶜ = 0

/-- the model: an environment together with a policy -/
structure Model (Θ S A : Type*) [MeasurableSpace S] [MeasurableSpace A] [Fintype A] where
  env : Env S A
  policy : Policy Θ S A

variable {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]

namespace Policy

/-- the action law `π_θ(· | x)` as a measure on `A` -/
noncomputable def measure (p : Policy Θ S A) (θ : Θ) (x : S) : Measure A :=
  ∑ a, ENNReal.ofReal (p.prob θ x a) • Measure.dirac a

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] in
instance (p : Policy Θ S A) (θ : Θ) (x : S) : IsProbabilityMeasure (p.measure θ x) := by
  constructor
  simp only [measure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ p.nonneg θ x a), p.sum_eq_one]
  simp

/-- the policy as a Markov kernel `S → A` -/
noncomputable def kernel (p : Policy Θ S A) (θ : Θ) : Kernel S A :=
  Kernel.ofFunOfCountable (p.measure θ)

omit [MeasurableSingletonClass A] in
instance (p : Policy Θ S A) (θ : Θ) : IsMarkovKernel (p.kernel θ) :=
  ⟨fun x ↦ inferInstanceAs (IsProbabilityMeasure (p.measure θ x))⟩

end Policy

namespace Model

variable (M : Model Θ S A)

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

omit [MeasurableSingletonClass A] in
/-- `M θ` is the trajectory law `M.traj θ` (it elaborates to `Model.traj M θ`). -/
noncomputable instance instCoeFun : CoeFun (Model Θ S A) (fun _ ↦ Θ → Measure (ℕ → ℝ × S × A)) where
  coe M := M.traj

/-- Infoview: print `Model.traj M θ` (also when written `M.traj θ`) as `M θ`. -/
@[app_unexpander Model.traj]
def traj.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M $θ) => `($M $θ)
  | _ => throw ()

set_option linter.unusedVariables false in
/-- State coordinate at time `t` on a trajectory `ω : ℕ → ℝ × S × A`
(`ω t = (r t, s t, a t)`). Dot notation: `M.stateAt t`.
Explicit `M` (unused) so field notation works; `variable (M)` would drop it. -/
def stateAt (M : Model Θ S A) (t : ℕ) : (ℕ → ℝ × S × A) → S :=
  fun ω ↦ (ω t).2.1

set_option linter.unusedVariables false in
/-- Action coordinate at time `t` on a trajectory. Dot notation: `M.actionAt t`. -/
def actionAt (M : Model Θ S A) (t : ℕ) : (ℕ → ℝ × S × A) → A :=
  fun ω ↦ (ω t).2.2

set_option linter.unusedVariables false in
/-- Reward coordinate at time `t` on a trajectory. Dot notation: `M.rewardAt t`.
No `SinglePSpace` instance: rewards live in `ℝ` (typically Lebesgue / not `CountableMeasure`). -/
def rewardAt (M : Model Θ S A) (t : ℕ) : (ℕ → ℝ × S × A) → ℝ :=
  fun ω ↦ (ω t).1

-- SinglePSpace instances for path projections. Binders follow `test_pspace_section.lean`:
-- `[CountableMeasure _]` supplies `MeasurableSpace` (no diamond with the outer section).
-- Separate sections so `stateAt` needs only `[CountableMeasure S]` and `actionAt` only `[CountableMeasure A]`.
section StateAtSinglePSpace
variable {Θ S A : Type*}
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  (M : Model Θ S A)

/-- Under `[CountableMeasure S]`, `M.stateAt t` is a `SinglePSpace` random variable on `M θ`. -/
instance stateAt.singlePSpace (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (M.stateAt t) :=
  Random.SinglePSpace.of.Measurable
    (measurable_fst.comp <| measurable_snd.comp <|
      (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t))
end StateAtSinglePSpace

section ActionAtSinglePSpace
variable {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  (M : Model Θ S A)

/-- Under `[CountableMeasure A]`, `M.actionAt t` is a `SinglePSpace` random variable on `M θ`. -/
instance actionAt.singlePSpace (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (M.actionAt t) :=
  Random.SinglePSpace.of.Measurable
    (measurable_snd.comp <| measurable_snd.comp <|
      (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t))
end ActionAtSinglePSpace

end Model

/-! ### `IsPolicyTrajectory` (HMM-style public path RVs)

Bundles the stage equality `∀ t, (· t) = (r t, s t, a t)` (same content as lemma `h₁`) so Random
public signatures can keep Fun binders `r` / `s` / `a` and write `(ℙ[M θ](s[0] = x) : ℝ)` without an
extra `hPs0` or a public `M.stateAt 0`. Measurability of `s t` / `a t` is recovered from `stage_eq` by
rewriting to the canonical pi-projections. -/

variable {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]

/-- Stage coordinates `(r[t], s[t], a[t])` match the trajectory point `ω t` for every `t`
(the binder that used to be written `h₁ : ∀ t, (· t) = (r t, s t, a t)`).

Under `[CountableMeasure S]` / `[CountableMeasure A]`, instances below give
`SinglePSpace (M θ) (s t)` / `(a t)` (and the joint `(s t, a t)`), so
`(ℙ[M θ](s[0] = x) : ℝ)` elaborates from `[IsPolicyTrajectory M r s a]` alone. -/
class IsPolicyTrajectory (M : Model Θ S A)
    (r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ)
    (s : ℕ ⇀ (ℕ → ℝ × S × A) → S)
    (a : ℕ ⇀ (ℕ → ℝ × S × A) → A) : Prop where
  /-- Same as lemma `h₁`: the stage map is the joint `(r t, s t, a t)`. -/
  stage_eq : ∀ t, (· t) = (r t, s t, a t)

namespace IsPolicyTrajectory

variable {M : Model Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}

/-- Canonical projections form an `IsPolicyTrajectory` (`stage_eq` by `rfl`). -/
instance instCanonical (M : Model Θ S A) :
    IsPolicyTrajectory M ⟨M.rewardAt⟩ ⟨M.stateAt⟩ ⟨M.actionAt⟩ where
  stage_eq t := by
    funext ω
    rfl

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] in
/-- `s t` is measurable: rewrite via `stage_eq` to `(ω t).2.1`. -/
theorem measurable_s [h : IsPolicyTrajectory M r s a] (t : ℕ) : Measurable (s t) := by
  have : s t = fun ω : ℕ → ℝ × S × A ↦ (ω t).2.1 :=
    funext fun ω ↦ (congrArg (fun z : ℝ × S × A ↦ z.2.1) (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_fst.comp <| measurable_snd.comp <|
    (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t)

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] in
/-- `a t` is measurable: rewrite via `stage_eq` to `(ω t).2.2`. -/
theorem measurable_a [h : IsPolicyTrajectory M r s a] (t : ℕ) : Measurable (a t) := by
  have : a t = fun ω : ℕ → ℝ × S × A ↦ (ω t).2.2 :=
    funext fun ω ↦ (congrArg (fun z : ℝ × S × A ↦ z.2.2) (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_snd.comp <| measurable_snd.comp <|
    (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t)

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] in
/-- `r t` is measurable: rewrite via `stage_eq` to `(ω t).1`. -/
theorem measurable_r [h : IsPolicyTrajectory M r s a] (t : ℕ) : Measurable (r t) := by
  have : r t = fun ω : ℕ → ℝ × S × A ↦ (ω t).1 :=
    funext fun ω ↦ (congrArg Prod.fst (congrFun (h.stage_eq t) ω)).symm
  rw [this]
  exact measurable_fst.comp (measurable_pi_apply (X := fun _ : ℕ ↦ ℝ × S × A) t)

end IsPolicyTrajectory

-- SinglePSpace from IsPolicyTrajectory. Separate sections so state needs only
-- `[CountableMeasure S]` and action only `[CountableMeasure A]` (same diamond avoidance as stateAt).
section IsPolicyTrajectoryState
variable {Θ S A : Type*}
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}

omit [MeasurableSingletonClass A] in
/-- Under `[IsPolicyTrajectory M r s a]` and `[CountableMeasure S]`, `s t` is a `SinglePSpace` RV on `M θ`. -/
theorem IsPolicyTrajectory.singlePSpace_s [h : IsPolicyTrajectory M r s a] (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (s t) :=
  Random.SinglePSpace.of.Measurable (h.measurable_s t)

end IsPolicyTrajectoryState

section IsPolicyTrajectoryAction
variable {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}

/-- Under `[IsPolicyTrajectory M r s a]` and `[CountableMeasure A]`, `a t` is a `SinglePSpace` RV on `M θ`. -/
theorem IsPolicyTrajectory.singlePSpace_a [h : IsPolicyTrajectory M r s a] (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (a t) :=
  Random.SinglePSpace.of.Measurable (h.measurable_a t)

end IsPolicyTrajectoryAction

section IsPolicyTrajectoryJoint
variable {Θ S A : Type*}
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}

/-- Joint `(s t, a t)`. Scoped: `r` is not in the conclusion (HMM-style). -/
theorem IsPolicyTrajectory.singlePSpace_sa [h : IsPolicyTrajectory M r s a] (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (s t, a t) :=
  Random.SinglePSpace.of.Measurable.Measurable
    (h.measurable_s t) (h.measurable_a t)

/-- Joint `(a t, s t)` (order used by some Random condProb / Grad lemmas). Scoped. -/
theorem IsPolicyTrajectory.singlePSpace_as [h : IsPolicyTrajectory M r s a] (θ : Θ) (t : ℕ) :
    SinglePSpace (M θ) (a t, s t) :=
  Random.SinglePSpace.of.Measurable.Measurable
    (h.measurable_a t) (h.measurable_s t)
end IsPolicyTrajectoryJoint

namespace IsPolicyTrajectory
-- `r` is often absent from the conclusion, so these are scoped (HMM `singlePSpace_y` pattern):
-- after `open IsPolicyTrajectory`, Lean finds `h` from the local `[IsPolicyTrajectory …]` binder.
set_option synthInstance.checkSynthOrder false in
attribute [scoped instance] singlePSpace_s singlePSpace_a singlePSpace_sa singlePSpace_as
end IsPolicyTrajectory

end PolicyGradient
