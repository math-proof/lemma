import Lemma.Random.RealPreimageSPreimageS_Add.eq.Pnkd.of.Ne0Real_Preimage.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a reachable state (`ℙ(s[t] = x) ≠ 0`), `ℙ(s[t+1] = y | s[t] = x) = Pnkd θ 1 x y`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {sₜ : 𝒮}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : (M.traj θ).real (s t ⁻¹' {sₜ}) ≠ 0)
  (y : 𝒮) :
-- imply
  (M.traj θ)[|s t ⁻¹' {sₜ}].real (s (t + 1) ⁻¹' {y}) = M.Pnkd θ 1 sₜ y :=
-- proof
  RealPreimageSPreimageS_Add.eq.Pnkd.of.Ne0Real_Preimage.All_EqWithDensity
    (M := M) h₀ h₁ 1 y


-- created on 2026-11-13
-- updated on 2026-11-16
