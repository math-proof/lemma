import sympy.stats.policy_trajectory
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Closed-form value functions of the policy-gradient model on a general (e.g. continuous) state space

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`).

The trajectory law `M θ` of `sympy.stats.policy_trajectory` needs a countable state space
(`Policy.kernel` is `Kernel.ofFunOfCountable`), and its value functions `M.V`, `M.Q` condition on the
events `s[t] = x`, which have probability `0` when `s[t]` has a continuous law.
On a general measurable state space `S` (e.g. `S = ℝ^b` with Lebesgue measure as `ReferenceMeasure`)
the conditional expectations `𝔼[· | s[t] = x]` of the sympy `Q_def`, `V_def` are therefore taken in the
regular (kernel) sense: they are the integrals against the transition kernel `M.env.trans` and the policy
`M.pol` of the same `Model`, unrolled from the state `x`:

* `rk x u = 𝔼[r[t] | s[t] = x, a[t] = u]` (the reward clamped to `[-R, R]`, almost surely equal to it);
* `Wk θ k x = 𝔼[r[t+k] | s[t] = x]`;
* `Vk θ γ x = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x] = ∑' k, γ ^ k * Wk θ k x`;
* `Qk θ γ x u = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x, a[t] = u] = rk x u + γ * ∫ Vk θ γ y ∂T(· | x, u)`;
* `P1k θ p x y = Pr(s[t+1] = y | s[t] = x)`, the density (w.r.t. a reference measure) of the next state
  when `p x u` is the density of `M.env.trans (x, u)`.

These are the continuous-state counterparts of `Model.W … M.rc`, `Model.Vc`, `Model.Qc`, `Model.P1`
(`sympy.stats.policy_trajectory.gradient`), which need `Fintype S`; the model is time-homogeneous, so
none of them depends on `t`.
-/
open MeasureTheory ProbabilityTheory Finset

namespace PolicyGradient

namespace Model

variable {Θ S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]

/-- `rk x u = 𝔼[r[t] | s[t] = x, a[t] = u]`, the expected reward clamped to `[-R, R]` -/
noncomputable def rk (M : Model Θ S A) (x : S) (u : A) : ℝ :=
  ∫ ρ, max (-M.env.R) (min M.env.R ρ) ∂(M.env.reward (x, u))

/-- `Wk θ k x = 𝔼[r[t+k] | s[t] = x]` on a general state space: one policy step and one transition per `k` -/
noncomputable def Wk (M : Model Θ S A) (θ : Θ) : ℕ → S → ℝ
  | 0 => fun x => ∑ u, M.pol.prob θ x u * M.rk x u
  | k + 1 => fun x => ∑ u, M.pol.prob θ x u * ∫ y, M.Wk θ k y ∂(M.env.trans (x, u))

/-- state value on a general state space: `Vk θ γ x = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x] = ∑' k, γ ^ k * Wk θ k x` -/
noncomputable def Vk (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  ∑' k, γ ^ k * M.Wk θ k x

/-- action value on a general state space:
`Qk θ γ x u = 𝔼[γ ** Stack[k](k) @ r[t:] | s[t] = x, a[t] = u] = rk x u + γ * ∫ y, Vk θ γ y ∂T(· | x, u)` -/
noncomputable def Qk (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  M.rk x u + γ * ∫ y, M.Vk θ γ y ∂(M.env.trans (x, u))

/-- `P1k θ p x y = Pr(s[t+1] = y | s[t] = x) = ∑ u, π_θ(u | x) * p(y | x, u)`, the next-state density
when `p x u` is a density of the transition `M.env.trans (x, u)` -/
noncomputable def P1k (M : Model Θ S A) (θ : Θ) (p : S → A → S → ℝ) (x y : S) : ℝ :=
  ∑ u, M.pol.prob θ x u * p x u y

end Model

end PolicyGradient
