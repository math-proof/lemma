import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.AeNormR.le.Abs_R
import Lemma.Random.Integrable_Mul_R.of.Measurable
import Lemma.Random.Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA
import Lemma.Random.Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc
import Lemma.Random.Integral_MulEqSAndEqAR.eq.MulMulRealProbSum_MulTW
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma E_ind_r [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] (M : Model Θ S A) (θ : Θ) (t k : ℕ) (x : S) (u : A) :
    ∫ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * reward (t + k) ω ∂(M θ) =
      ((M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u) *
      ∫ ω, reward (t + k) ω ∂(M θ)[|state t ⁻¹' {x} ∩ action t ⁻¹' {u}] := by
  by_cases h : (M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u = 0
  · rw [h, zero_mul]
    cases k with
    | zero => rw [add_zero, Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc, h, zero_mul]
    | succ j => rw [Integral_MulEqSAndEqAR.eq.MulMulRealProbSum_MulTW, h, zero_mul]
  · rw [Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA, mul_inv_cancel_left₀ h]

/--
`𝔼[1{s[t] = x ∧ a[t] = u} * G[t]] = Pr(s[t] = x) * π_θ(u | x) * Q θ γ t x u`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (x : S)
  (u : A) :
-- imply
  ∫ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * G γ t ω ∂(M θ) =
    ((M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u) * M.Q θ γ t x u := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (state t ω, action t ω)) := (Random.Measurable_S t).prodMk (Random.Measurable_A t)
  let φ : S × A → ℝ := fun p => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0
  have hF : ∀ k, Integrable (fun ω => (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) *
      (γ ^ k * reward (t + k) ω)) (M θ) := fun k =>
    ((Integrable_Mul_R.of.Measurable (M := M) _ hX θ φ (t + k)).const_mul (γ ^ k)).congr
      (ae_of_all _ fun ω => by simp only [φ]; ring)
  have hN : ∀ k, ∫ ω, ‖(if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * (γ ^ k * reward (t + k) ω)‖
      ∂(M θ) ≤ γ ^ k * |M.env.R| := by
    intro k
    have hb : ∀ᵐ ω ∂(M θ), ‖‖(if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) *
        (γ ^ k * reward (t + k) ω)‖‖ ≤ γ ^ k * |M.env.R| := by
      filter_upwards [AeNormR.le.Abs_R (M := M) θ] with ω h
      rw [norm_norm, norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact (mul_le_of_le_one_left (mul_nonneg (pow_nonneg h₀.1 k) (norm_nonneg _))
        (by split_ifs <;> simp)).trans (mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k))
    have := norm_integral_le_of_norm_le_const hb
    simp only [probReal_univ, mul_one] at this
    exact (Real.le_norm_self _).trans this
  have hS : Summable (fun k => ∫ ω, ‖(if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) *
      (γ ^ k * reward (t + k) ω)‖ ∂(M θ)) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) hN
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right _)
  have e : ∀ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * G γ t ω =
      ∑' k, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * (γ ^ k * reward (t + k) ω) := fun ω => by
    rw [tsum_mul_left]; rfl
  simp_rw [e]
  rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
  have e2 : ∀ k, ∫ ω, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * (γ ^ k * reward (t + k) ω) ∂(M θ) =
      ((M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u) *
        (γ ^ k * ∫ ω, reward (t + k) ω ∂(M θ)[|state t ⁻¹' {x} ∩ action t ⁻¹' {u}]) := fun k => by
    rw [show (fun ω => (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * (γ ^ k * reward (t + k) ω)) =
      fun ω => γ ^ k * ((if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * reward (t + k) ω) from
        funext fun ω => by ring, integral_const_mul, E_ind_r]
    ring
  simp_rw [e2]
  rw [tsum_mul_left]
  rfl


-- created on 2026-10-06
