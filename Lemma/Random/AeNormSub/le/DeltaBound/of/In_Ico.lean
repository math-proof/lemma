import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
Almost surely every temporal-difference residual `δ[j] = r[j] + γ * V0(s[j+1]) - V0(s[j])`
is bounded by `(3 / (1 - γ) - 1) * |R|`. Remigrated onto `DensityModel` (applies dens twin).
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ j, ‖r j ω + γ * M.V0 θ γ (s (j + 1) ω) - M.V0 θ γ (s j ω)‖ ≤
    (3 / (1 - γ) - 1) * |M.env.R| := by
-- proof
  exact AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity h₀ h₁ θ


-- created on 2026-10-21
-- updated on 2026-11-04
