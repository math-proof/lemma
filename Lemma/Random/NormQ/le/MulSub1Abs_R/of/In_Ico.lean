import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory Topology Filter PolicyGradient PolicyGradient.DensityModel Random


/--
On atoms of positive mass, the action value is bounded: `‖Q θ γ t x u‖ ≤ (1 - γ)⁻¹ * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
  {u : 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hpos : (M θ) (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) ≠ 0) :
-- imply
  let Q (θ : Θ) (t : ℕ) (x : 𝒮) (u : 𝒜) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x ∧ a t = u);
  ‖Q θ t x u‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hy : Measurable (s t, a t) :=
    (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
      (Random.Measurable.of.All_Eq.snd.snd h₁ t)
  have hfG : Measurable
    (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hpre : (s t, a t) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
    ext ω
    simp [JointRandomSymbol]
  have hmap : (M θ).map (s t, a t) {(x, u)} ≠ 0 := by
    rwa [Measure.map_apply hy (measurableSet_singleton (x, u)), hpre]
  simp only [Expectation.asRV_process]
  rw [Expectation.condEval_eq_integral hpR hy hfG hmap]
  rw [hpre]
  show ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω
    ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}]‖ ≤ _
  have hbound : ∀ᵐ ω ∂(M θ),
    ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ θ] with ω h
    apply tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _)
    intro k
    change ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R|
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg h₀.1 k)]
    apply mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
  have hae : ∀ᵐ ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}],
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    cond_absolutelyContinuous.ae_le hbound
  have := cond_isProbabilityMeasure (μ := M θ) hpos
  simpa using norm_integral_le_of_norm_le_const hae


-- created on 2026-10-06
-- updated on 2026-11-14
