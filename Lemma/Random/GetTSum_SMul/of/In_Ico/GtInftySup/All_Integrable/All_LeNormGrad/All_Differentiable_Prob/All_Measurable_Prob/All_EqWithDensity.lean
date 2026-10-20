import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormWkd.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Set


private lemma Er_bdd
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
  ‖∫ ω, r t ω ∂(M θ)‖ ≤ |M.env.R| := by
  have := M.env.init_prob
  rw [Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity (M := M) h₀ θ t]
  have h := norm_integral_le_of_norm_le_const (μ := M.env.init)
    (Filter.Eventually.of_forall fun x => NormWkd.le.Abs_R (M := M) θ t x)
  simpa using h

/--
`∇ ∑' t, γ ^ t * 𝔼[r[t]] = ∑' t, γ ^ t • ∇ 𝔼[r[t]]` (continuous-action model).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
  {g : S → A → ℝ}
  {Cg : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ))
    (∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) θ := by
-- proof
  have hD := fun t =>
    Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₁ hπ h₂ h₃ h₄ h₅ t
  refine hasFDerivAt_tsum (x₀ := θ)
    (Summable_MulPowMulAdd_1.of.In_Ico h₀ (Cg * |M.env.R|))
    (fun t θ => ((hD t).1 θ).hasFDerivAt.const_mul (γ ^ t))
    (fun t θ => ?_) ?_ θ
  ·
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left ((hD t).2 θ) (pow_nonneg h₀.1 t)
  ·
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|) fun t => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (Er_bdd h₁ θ t) (pow_nonneg h₀.1 t)


-- created on 2026-10-20
