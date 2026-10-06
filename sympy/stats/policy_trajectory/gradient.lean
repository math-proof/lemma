import sympy.stats.policy_trajectory.markov
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Differentiability API for the policy-gradient trajectory model

Facts about `PolicyGradient.Model` used by the policy-gradient lemmas
(`Tensor.EqGrad.*.policy_gradient.*`, `Tensor.Eq.Grad.Expect.*.policy_gradient`, …), under the
hypotheses that every `θ ↦ π_θ(u | x)` is differentiable with a globally bounded gradient:

* `Pn θ n x y = Pr(s[t+n] = y | s[t] = x)` and `P1 θ x y = Pr(s[t+1] = y | s[t] = x)`, the
  Chapman–Kolmogorov identity `Pn_succ'`, and `Pr(s[t] = y) = ∑ x, Pr(s[0] = x) * Pn θ t x y`;
* differentiability and gradient bounds of the kernel expectations `W` (`W_diff`);
* the time-free closed forms `Vc`, `Qc` of the value functions, their differentiability and the
  gradient of the Bellman equation (`grad_Vc`);
* local agreement of `M.V` with `Vc` on reachable states, and the finite-sum form of expectations
  of functions of `(s[t], a[t])`.

No `Lemma.*` module is imported here.
-/
open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace PolicyGradient

namespace Model

variable {Θ S A : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- `Pn θ n x y = Pr(s[t+n] = y | s[t] = x)` (time-homogeneous `n`-step state transition) -/
noncomputable def Pn (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) : ℝ :=
  M.W θ (fun z => if z.2.1 = y then (1:ℝ) else 0) n x

/-- `P1 θ x y = Pr(s[t+1] = y | s[t] = x) = ∑ u, π_θ(u | x) * T(x, u, y)` -/
noncomputable def P1 (M : Model Θ S A) (θ : Θ) (x y : S) : ℝ :=
  ∑ u, M.pol.prob θ x u * M.T x u y

/-- time-free closed form of the state-value function: `Vc θ γ x = ∑' k, γ ^ k * 𝔼[r[t+k] | s[t] = x]` -/
noncomputable def Vc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  ∑' k, γ ^ k * M.W θ M.rc k x

/-- time-free closed form of the action-value function:
`Qc θ γ x u = 𝔼[r | x, u] + γ * ∑ y, T(x, u, y) * Vc θ γ y` -/
noncomputable def Qc (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  (∫ ρ, M.rc (ρ, x, u) ∂(M.env.reward (x, u))) + γ * ∑ y, M.T x u y * M.Vc θ γ y

omit [DecidableEq A] in
theorem V_eq_Vc (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) (x : S)
    (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0) : M.V θ γ t x = M.Vc θ γ x :=
  V_eq M θ hγ t x hP

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem r_bdd_ae (M : Model Θ S A) (θ : Θ) :
    ∀ᵐ ω ∂(M θ), ∀ k, ‖r k ω‖ ≤ |M.env.R| := by
  rw [ae_all_iff]
  exact fun k => (r_ae M θ k).mono fun ω h => by rw [h]; exact rc_bdd M _

omit [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] in
theorem r_meas (k : ℕ) : Measurable (r (S := S) (A := A) k) :=
  measurable_fst.comp (measurable_pi_apply k)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem ind_smul_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ)
    (ω : ℕ → ℝ × S × A) (c : ℝ) (ψ : S → A → E) :
    c • ψ (s t ω) (a t ω) =
      ∑ x, ∑ u, ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * c) • ψ x u := by
  rw [Finset.sum_eq_single (s t ω) (fun b _ hb => Finset.sum_eq_zero fun u _ => by simp [Ne.symm hb])
    (by simp)]
  rw [Finset.sum_eq_single (a t ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

end Model

end PolicyGradient
