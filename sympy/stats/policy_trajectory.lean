import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import sympy.stats.variance
import sympy.stats.ennreal_coe

/-!
# Shared trajectory model for the policy-gradient lemmas (standard MDP)

Lean model behind the sympy symbols used in `Tensor.*.policy_gradient_theorem`,
`Tensor.*.unbiased_advantage_estimate` and their dependencies:

* `s : ℕ → Ω → S` (states), `a : ℕ → Ω → A` (actions), `r : ℕ → Ω → ℝ` (rewards),
  with `S` and `A` finite;
* `π` (the trainable weights) is a point `θ` of a real normed space `Θ`;
* `Pr[a:π](a[t] | s[t])` is the policy `M.pol.prob θ (s t) (a t)`;
* `Expectation[r, a:π](f)` is the Bochner integral `∫ ω, f ω ∂(M.traj θ)`;
* `Expectation[...](f | s[t] = x)` is the integral against Mathlib's conditional measure
  `(M.traj θ)[| s t ⁻¹' {x}]`;
* `γ ** Stack[k](k) @ r[t:]` is `∑' k, γ ^ k * r (t + k)`;
* `Derivative[π]` is `fderiv ℝ · θ`.

The environment is a standard (time-homogeneous) MDP: `s 0 ∼ init`, `a t ∼ π_θ(· | s t)`,
`r t ∼ reward (s t, a t)`, `s (t + 1) ∼ trans (s t, a t)`, rewards bounded by `R`.
The stage process `ω t = (s t, a t, r t)` is a time-homogeneous Markov chain on `S × A × ℝ`
with kernel `M.K θ`; its law `M.traj θ` is Mathlib's Ionescu-Tulcea measure `Kernel.trajMeasure`
on `ℕ → S × A × ℝ`.  The sympy reward hypothesis `Equal(r[t] | s[:t] & a[:t], r[t])` is not
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
  pol : Policy Θ S A

/-- state at time `t` -/
def s {S A : Type*} (t : ℕ) (ω : ℕ → S × A × ℝ) : S := (ω t).1
/-- action at time `t` -/
def a {S A : Type*} (t : ℕ) (ω : ℕ → S × A × ℝ) : A := (ω t).2.1
/-- reward at time `t` -/
def r {S A : Type*} (t : ℕ) (ω : ℕ → S × A × ℝ) : ℝ := (ω t).2.2

/-- discounted return from time `t`: `γ ** Stack[k](k) @ r[t:]` -/
noncomputable def G {S A : Type*} (γ : ℝ) (t : ℕ) (ω : ℕ → S × A × ℝ) : ℝ :=
  ∑' k, γ ^ k * r (t + k) ω

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

/-- law of one stage `(s, a, r)` given its state `s`: `a ∼ π_θ(· | s)`, `r ∼ reward (s, a)` -/
noncomputable def stageK (θ : Θ) : Kernel S (S × A × ℝ) :=
  Kernel.deterministic id measurable_id ×ₖ (M.pol.kernel θ ⊗ₖ M.env.reward)

instance (θ : Θ) : IsMarkovKernel (M.stageK θ) := by
  have := M.env.reward_markov
  unfold stageK; infer_instance

/-- transition kernel of the stage chain: `(s, a, r) ↦` law of the next stage -/
noncomputable def K (θ : Θ) : Kernel (S × A × ℝ) (S × A × ℝ) :=
  M.stageK θ ∘ₖ M.env.trans.comap (fun z ↦ (z.1, z.2.1)) (by fun_prop)

instance (θ : Θ) : IsMarkovKernel (M.K θ) := by
  have := M.env.trans_markov
  unfold K; infer_instance

/-- `j`-step kernel expectation of `f` along the stage chain: `z ↦ 𝔼[f (ω (t + j)) | ω t = z]` -/
noncomputable def Kf (θ : Θ) (f : S × A × ℝ → ℝ) : ℕ → S × A × ℝ → ℝ
  | 0 => f
  | j + 1 => fun z ↦ ∫ w, Kf θ f j w ∂(M.K θ z)

/-- `y ↦ 𝔼[f (ω (t + j)) | s t = y]`, the same for every time `t` (time-homogeneous chain) -/
noncomputable def W (θ : Θ) (f : S × A × ℝ → ℝ) (j : ℕ) (y : S) : ℝ :=
  ∫ z, M.Kf θ f j z ∂(M.stageK θ y)

/-- law of the first stage -/
noncomputable def μ₀ (θ : Θ) : Measure (S × A × ℝ) := M.stageK θ ∘ₘ M.env.init

instance (θ : Θ) : IsProbabilityMeasure (M.μ₀ θ) := by
  have := M.env.init_prob
  unfold μ₀; infer_instance

/-- the stage chain seen as history-dependent kernels (only the last stage matters) -/
noncomputable def step (θ : Θ) (n : ℕ) : Kernel (Π _ : Iic n, S × A × ℝ) (S × A × ℝ) :=
  (M.K θ).comap (fun h ↦ h ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (θ : Θ) (n : ℕ) : IsMarkovKernel (M.step θ n) := by
  unfold step; infer_instance

/-- law of the whole trajectory under the weights `θ` (Ionescu-Tulcea) -/
noncomputable def traj (θ : Θ) : Measure (ℕ → S × A × ℝ) :=
  Kernel.trajMeasure (X := fun _ ↦ S × A × ℝ) (M.μ₀ θ) (M.step θ)

instance (θ : Θ) : IsProbabilityMeasure (M.traj θ) := by
  unfold traj; infer_instance

/-- the reward coordinate of a stage clamped to `[-R, R]` (almost surely equal to it) -/
noncomputable def rc (z : S × A × ℝ) : ℝ := max (-M.env.R) (min M.env.R z.2.2)

/-- transition probability `Pr(s[t+1] = y | s[t] = x, a[t] = u)` -/
noncomputable def T (x : S) (u : A) (y : S) : ℝ := (M.env.trans (x, u)).real {y}

/-- `Pr[a:π](a[t] = u | s[t] = x)`: the policy probability -/
def Pr (θ : Θ) (x : S) (u : A) : ℝ := M.pol.prob θ x u

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [Fintype A] in
theorem r_meas' (t : ℕ) : Measurable (r (S := S) (A := A) t) :=
  measurable_snd.comp (measurable_snd.comp (measurable_pi_apply t))

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [Fintype A] in
theorem G_meas (γ : ℝ) (t : ℕ) : Measurable (G (S := S) (A := A) γ t) :=
  Measurable.tsum fun k => (r_meas' (t + k)).const_mul (γ ^ k)

/-- state-value function `V(s[t] = x) = 𝔼[G[t] | s[t] = x] = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x]`,
the expectation of the return `G[t]` under the conditional law `(M.traj θ)[| s t ⁻¹' {x}]`
(`0` at unreachable `x`, where that measure is not a probability measure) -/
noncomputable def V (θ : Θ) (γ : ℝ) (t : ℕ) (x : S) : ℝ :=
  if h : (M.traj θ) (s t ⁻¹' {x}) ≠ 0 then
    haveI : IsProbabilityMeasure ((M.traj θ)[|s t ⁻¹' {x}]) := cond_isProbabilityMeasure h
    haveI : PSpace ((M.traj θ)[|s t ⁻¹' {x}]) (G (S := S) (A := A) γ t) :=
      ⟨(G_meas γ t).aemeasurable⟩
    let R := G (S := S) (A := A) γ t
    𝔼[R : (M.traj θ)[|s t ⁻¹' {x}]](R)
  else 0

omit [MeasurableSingletonClass A] in
/-- `V` is the Bochner integral of `G` against the conditional measure (also at unreachable `x`,
where the conditional measure is `0`) -/
theorem V_eq_integral (θ : Θ) (γ : ℝ) (t : ℕ) (x : S) :
    M.V θ γ t x = ∫ ω, G γ t ω ∂(M.traj θ)[|s t ⁻¹' {x}] := by
  unfold V
  by_cases h : (M.traj θ) (s t ⁻¹' {x}) ≠ 0
  · rw [dif_pos h]
    have : IsProbabilityMeasure ((M.traj θ)[|s t ⁻¹' {x}]) := cond_isProbabilityMeasure h
    have : PSpace ((M.traj θ)[|s t ⁻¹' {x}]) (G (S := S) (A := A) γ t) :=
      ⟨(G_meas γ t).aemeasurable⟩
    exact Expectation.ofRV_self _ _
  · rw [dif_neg h, not_not.1 h |> cond_eq_zero_of_meas_eq_zero]
    simp

/-- action-value function `Q(s[t] = x, a[t] = u) = γ ** Stack[k](k) @ 𝔼[r[t:] | s[t] = x ∧ a[t] = u]` -/
noncomputable def Q (θ : Θ) (γ : ℝ) (t : ℕ) (x : S) (u : A) : ℝ :=
  ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[| s t ⁻¹' {x} ∩ a t ⁻¹' {u}]

end Model

end PolicyGradient
