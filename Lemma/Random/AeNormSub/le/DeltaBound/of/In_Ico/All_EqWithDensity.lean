import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
Almost surely every temporal-difference residual
`δ[j] = r[j] + γ * V0(s[j+1]) - V0(s[j])` is bounded by `(3 / (1 - γ) - 1) * |R|`
(continuous-action model).
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
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ j, ‖r j ω + γ * M.V0 θ γ (s (j + 1) ω) - M.V0 θ γ (s j ω)‖ ≤
    (3 / (1 - γ) - 1) * |M.env.R| := by
-- proof
  filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ] with ω hr j
  calc
    _ ≤ ‖r j ω‖ + ‖γ * M.V0 θ γ (s (j + 1) ω)‖ + ‖M.V0 θ γ (s j ω)‖ :=
      (norm_sub_le _ _).trans (by gcongr; apply norm_add_le)
    _ ≤ (3 / (1 - γ) - 1) * |M.env.R| := by
      rw [norm_mul, Real.norm_of_nonneg h₀.1]
      apply le_trans
      ·
        apply add_le_add
        ·
          apply add_le_add (hr j)
          apply mul_le_mul_of_nonneg_left
          · apply NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀
          · apply h₀.1
        · apply NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀
      ·
        have hpos : 0 < 1 - γ := sub_pos.mpr h₀.2
        refine (le_of_eq (b := (2 * (1 - γ)⁻¹) * |M.env.R|) ?_).trans ?_
        ·
          field_simp [hpos.ne']
          ring
        ·
          gcongr
          field_simp [hpos.ne']
          linarith [h₀.1]


-- created on 2026-10-20
-- updated on 2026-11-11
