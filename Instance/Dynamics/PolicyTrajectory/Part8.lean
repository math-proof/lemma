import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.Probability.Moments.Variance
import Instance.Analysis.Real.Numbers
import Theorem.Algebra.Power.Part2
import Theorem.Data.Vector.Basic.Part2
import Def.Data.List.List.Basic
import Theorem.Function
import Lemma.Random.SinglePSpace.of.Measurable
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
import Class.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Finset

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


namespace PolicyGradient

variable {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]

variable {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]

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

end IsPolicyTrajectory
end PolicyGradient
