import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
open MeasureTheory Finset Filter PolicyGradient PolicyGradient.DensityModel Random


/--
The discounted return `G[t]` is integrable under the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  Integrable ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) (M θ) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  have hsum : ∀ᵐ ω ∂(M θ),
      HasSum (fun k => γ ^ k * r (t + k) ω) (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω) ∧
        ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (r := r)
      (s := fun t ω ↦ (ω t).2.1) (a := fun t ω ↦ (ω t).2.2) (fun _ ↦ rfl) θ] with ω h
    have hb : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      apply mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
    refine And.intro ?_ ?_
    ·
      apply (Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right _) hb).hasSum
    ·
      apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) hb
  refine Integrable.of_bound ?_ ((1 - γ)⁻¹ * |M.env.R|) ?_
  ·
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n ω => ∑ k ∈ range n, γ ^ k * (ω (t + k)).1) (fun n => ?_) ?_
    ·
      apply (measurable_fun_sum _ fun k _ =>
        (measurable_fst.comp (measurable_pi_apply (t + k))).const_mul (γ ^ k)).aestronglyMeasurable
    ·
      apply hsum.mono
      intro ω h
      apply h.1.tendsto_sum_nat
  ·
    apply hsum.mono
    intro ω h
    apply h.2


-- created on 2026-10-06
-- updated on 2026-11-14
