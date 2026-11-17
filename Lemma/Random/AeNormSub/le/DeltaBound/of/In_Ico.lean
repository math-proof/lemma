import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Almost surely every temporal-difference residual `δ[j] = r[j] + γ * V0(s[j+1]) - V0(s[j])`
is bounded by `(3 / (1 - γ) - 1) * |R|`. Remigrated onto `Model` (applies dens twin).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M.traj θ), ∀ j, ‖r j ω + γ * M.V0 θ γ (s (j + 1) ω) - M.V0 θ γ (s j ω)‖ ≤
    (3 / (1 - γ) - 1) * |M.R| := by
-- proof
  exact AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity h₀ h₁ θ


-- created on 2026-10-21
-- updated on 2026-11-16