import Lemma.Random.ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory


@[path]
private lemma main
  [μ : ReferenceMeasure 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ} {t : ℕ} {sₜ : 𝒮} {aₜ : 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : Model.IsPolicyTrajectory M r s a)
  (h₁ : Model.AbsContJointAS M a s)
  (h₂ : (M.traj θ).prob (a t, s t) (aₜ, sₜ) =
    ENNReal.ofReal (M.π[θ] sₜ aₜ) *
      ((M.traj θ).map (s t)).rnDeriv (μ.measure : Measure 𝒮) sₜ)
  (h₃ : ((M.traj θ).map (s t)).rnDeriv (μ.measure : Measure 𝒮) sₜ ≠ 0)
  (h₄ : ((M.traj θ).map (s t)).rnDeriv (μ.measure : Measure 𝒮) sₜ ≠ ⊤) :
-- imply
  have : SinglePSpace (M.traj θ) (a t, s t) := h₀.singlePSpace_as (haj := h₁) θ t
  (ℙ[M.traj θ]((a t) = aₜ | (s t) = sₜ) : ℝ) = M.π[θ] sₜ aₜ := by
-- proof
  intro hP
  have hENN :
    ℙ[M.traj θ]((a t) = aₜ | (s t) = sₜ) =
      ENNReal.ofReal (M.π[θ] sₜ aₜ) :=
    ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity (M := M) h₀ h₁ h₂ h₃ h₄
  rw [hENN]
  exact ENNReal.toReal_ofReal (hStoch.nonneg θ sₜ aₜ)


-- created on 2026-10-21
-- updated on 2026-11-17
