import Def.Dynamics.PolicyTrajectory.Continuous
import Def.Order.Miscellaneous
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
open MeasureTheory PolicyGradient Finset


namespace PolicyGradient.Model

/-- One-step state transition `∑ u, π_θ(u | x) * T(x, u, y)`. -/
noncomputable def P1
  {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  (M : Model Θ S A) (θ : Θ) (x y : S) : ℝ :=
  ∑ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y}

/-- Expected reward at `(x, u)`, clamped to `[-R, R]`. -/
noncomputable def rk
  {Θ S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  (M : Model Θ S A) (x : S) (u : A) : ℝ :=
  ∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (x, u))

/-- Finite-action k-step expected reward from a state. -/
noncomputable def Wk
  {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  (M : Model Θ S A) (θ : Θ) : ℕ → S → ℝ
  | 0 => fun y => ∑ u, M.policy.prob θ y u * M.rk y u
  | k + 1 => fun y => ∑ u, M.policy.prob θ y u * ∫ y', M.Wk θ k y' ∂(M.env.trans (y, u))

/-- Discounted state value `∑' k, γ ^ k * Wk θ k x`. -/
noncomputable def V0
  {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) : ℝ :=
  ∑' k, γ ^ k * M.Wk θ k x

/-- Discounted state value as a function of the state, the same series as `V0`. -/
noncomputable def Vk
  {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  (M : Model Θ S A) (θ : Θ) (γ : ℝ) : S → ℝ :=
  fun x => M.V0 θ γ x

/-- Action value `rk x u + γ * 𝔼[Vk | s = x, a = u]`. -/
noncomputable def Qk
  {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  (M : Model Θ S A) (θ : Θ) (γ : ℝ) (x : S) (u : A) : ℝ :=
  M.rk x u + γ * ∫ y, M.Vk θ γ y ∂(M.env.trans (x, u))

/-- Time-homogeneous value: `V θ γ t x = V0 θ γ x`. -/
noncomputable def V
  {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  (M : Model Θ S A) (θ : Θ) (γ : ℝ) (_ : ℕ) (x : S) : ℝ :=
  M.V0 θ γ x

end PolicyGradient.Model


/--
`x ↦ rk x u = 𝔼[r[t] | s[t] = x, a[t] = u]` is measurable (the reward is a kernel on `S × A`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (u : A) :
-- imply
  Measurable (fun x => M.rk x u) := by
-- proof
  have := M.env.reward_markov
  simp only [Model.rk]
  apply (StronglyMeasurable.integral_kernel_prod_right (κ := M.env.reward.comap (fun x => (x, u)) (by fun_prop))
    (f := fun (_ : S) (ρ : ℝ) => clip ρ (-M.env.R) M.env.R) _).measurable
  unfold clip
  apply ((measurable_snd.max measurable_const).min measurable_const).stronglyMeasurable


-- created on 2026-10-07
-- updated on 2026-11-08
