import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory Topology Filter PolicyGradient PolicyGradient.DensityModel Random


/--
On atoms of positive mass, the state-value function is bounded by the discounted reward bound:
`‖V θ t x‖ ≤ (1 - γ)⁻¹ * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hpos : (M θ) (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let V (θ : Θ) (t : ℕ) (x : 𝒮) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x);
  ‖V θ t x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁ t
  have hfG : Measurable
    (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hmap : (M θ).map (s t) {x} ≠ 0 := by
    rwa [Measure.map_apply hs (measurableSet_singleton x)]
  simp only [Expectation.asRV_process]
  rw [Expectation.condEval_eq_integral hpR hs hfG hmap]
  show ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x}]‖ ≤ _
  have hbound : ∀ᵐ ω ∂(M θ),
    ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ θ] with ω h
    apply tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _)
    intro k
    change ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R|
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg h₀.1 k)]
    apply mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
  have hae : ∀ᵐ ω ∂(M θ)[|s t ⁻¹' {x}],
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    cond_absolutelyContinuous.ae_le hbound
  have := cond_isProbabilityMeasure (μ := M θ) hpos
  simpa using norm_integral_le_of_norm_le_const hae


-- created on 2026-10-06
-- updated on 2026-11-14
