import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Norm_Integral_R.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
The action value is bounded: `‖Q θ γ t x u‖ ≤ (1 - γ)⁻¹ * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A) :
-- imply
  ‖M.Q r s a θ γ t x u‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  unfold Model.Q
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
  exact mul_le_mul_of_nonneg_left (Norm_Integral_R.le.Abs_R h₁ (M := M) θ _ (t + k)) (pow_nonneg h₀.1 k)


-- created on 2026-10-06
