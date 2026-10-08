import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.AeNormR.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
Almost surely the discounted return `G[t] = ∑' k, γ ^ k * r[t+k]` converges and `‖G[t]‖ ≤ (1 - γ)⁻¹ * |R|`.
-/
@[main]
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
  (t : ℕ) :
-- imply
  ∀ᵐ ω ∂(M θ), HasSum (fun k => γ ^ k * r (t + k) ω) (G r γ t ω) ∧
    ‖G r γ t ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  filter_upwards [Random.AeNormR.le.Abs_R h₁ (M := M) θ] with ω h
  have hb : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
  have hs : Summable (fun k => γ ^ k * r (t + k) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right _) hb
  exact ⟨hs.hasSum, tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) hb⟩


-- created on 2026-10-06
