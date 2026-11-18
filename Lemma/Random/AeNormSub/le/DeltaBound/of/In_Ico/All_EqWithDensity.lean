import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Almost surely every temporal-difference residual
`δ[j] = r[j] + γ * V0(s[j+1]) - V0(s[j])` is bounded by `(3 / (1 - γ) - 1) * |R|`
(continuous-action model).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ j, ‖r j ω + γ * M.V0 R θ γ (s (j + 1) ω) - M.V0 R θ γ (s j ω)‖ ≤
    (3 / (1 - γ) - 1) * |R| := by
-- proof
  filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) hR θ] with ω hr j
  calc
    _ ≤ ‖r j ω‖ + ‖γ * M.V0 R θ γ (s (j + 1) ω)‖ + ‖M.V0 R θ γ (s j ω)‖ :=
      (norm_sub_le _ _).trans (by gcongr; apply norm_add_le)
    _ ≤ (3 / (1 - γ) - 1) * |R| := by
      rw [norm_mul, Real.norm_of_nonneg h₀.1]
      apply le_trans
      ·
        apply add_le_add
        ·
          apply add_le_add (hr j)
          apply mul_le_mul_of_nonneg_left
          · apply NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ R
          · apply h₀.1
        · apply NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ R
      ·
        have hpos : 0 < 1 - γ := sub_pos.mpr h₀.2
        refine (le_of_eq (b := (2 * (1 - γ)⁻¹) * |R|) ?_).trans ?_
        ·
          field_simp [hpos.ne']
          ring
        ·
          gcongr
          field_simp [hpos.ne']
          linarith [h₀.1]


-- created on 2026-10-20
-- updated on 2026-11-18