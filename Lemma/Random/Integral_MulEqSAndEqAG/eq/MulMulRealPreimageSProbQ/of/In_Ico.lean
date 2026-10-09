import sympy.stats.policy_trajectory.gradient
import Lemma.Random.AeNormR.le.Abs_R
import Lemma.Random.Integrable_Mul_R.of.Measurable
import Lemma.Random.Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA
import Lemma.Random.Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc
import Lemma.Random.Integral_MulEqSAndEqAR.eq.MulMulRealProbSum_MulTW
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma E_ind_r [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] {r : ℕ → (ℕ → ℝ × S × A) → ℝ} {s : ℕ → (ℕ → ℝ × S × A) → S} {a : ℕ → (ℕ → ℝ × S × A) → A} (h₁ : ∀ t, (· t) = (r t, s t, a t)) (M : Model Θ S A) (θ : Θ) (t k : ℕ) (x : S) (u : A) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + k) ω ∂(M θ) =
      ((M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u) *
      ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
  by_cases h : (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u = 0
  · rw [h, zero_mul]
    cases k with
    | zero => rw [add_zero, Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc h₁, h, zero_mul]
    | succ j => rw [Integral_MulEqSAndEqAR.eq.MulMulRealProbSum_MulTW h₁, h, zero_mul]
  · rw [Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA h₁, mul_inv_cancel_left₀ h]

/--
`𝔼[1{s[t] = x ∧ a[t] = u} * G[t]] = Pr(s[t] = x) * π_θ(u | x) * Q θ γ t x u`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
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
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ) =
    ((M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u) * M.Q r s a θ γ t x u := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (Random.Measurable_S h₁ t).prodMk (Random.Measurable_A h₁ t)
  let φ : S × A → ℝ := fun p => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0
  have hF : ∀ k, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (γ ^ k * r (t + k) ω)) (M θ) := fun k =>
    ((Integrable_Mul_R.of.Measurable h₁ (M := M) _ hX θ φ (t + k)).const_mul (γ ^ k)).congr
      (ae_of_all _ fun ω => by simp only [φ]; ring)
  have hN : ∀ k, ∫ ω, ‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω)‖
      ∂(M θ) ≤ γ ^ k * |M.env.R| := by
    intro k
    have hb : ∀ᵐ ω ∂(M θ), ‖‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (γ ^ k * r (t + k) ω)‖‖ ≤ γ ^ k * |M.env.R| := by
      filter_upwards [AeNormR.le.Abs_R h₁ (M := M) θ] with ω h
      rw [norm_norm, norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact (mul_le_of_le_one_left (mul_nonneg (pow_nonneg h₀.1 k) (norm_nonneg _))
        (by split_ifs <;> simp)).trans (mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k))
    have := norm_integral_le_of_norm_le_const hb
    simp only [probReal_univ, mul_one] at this
    exact (Real.le_norm_self _).trans this
  have hS : Summable (fun k => ∫ ω, ‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (γ ^ k * r (t + k) ω)‖ ∂(M θ)) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) hN
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right _)
  have e : ∀ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω =
      ∑' k, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω) := fun ω => by
    dsimp only [Dot.dot, Function.getSliceFrom]
    simp only [Function.hPow_apply, id_eq]
    rw [← tsum_mul_left]
  refine (integral_congr_ae (Filter.Eventually.of_forall e)).trans ?_
  rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
  have e2 : ∀ k, ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω) ∂(M θ) =
      ((M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u) *
        (γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}]) := fun k => by
    rw [show (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω)) =
      fun ω => γ ^ k * ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + k) ω) from
        funext fun ω => by ring, integral_const_mul, E_ind_r h₁]
    ring
  simp_rw [e2]
  rw [tsum_mul_left]
  rfl


-- created on 2026-10-06
