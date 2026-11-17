import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory


/--
Continuous-action bridge between the `ℙ` binder sugar and a density policy:
given absolute continuity of `law(a[t], s[t])` (so `SinglePSpace` elaborates) and a
pointwise factorization of the joint density into policy dens × state RN derivative,
the conditional density `ℙ[M.traj θ](a[t] = u | s[t] = x)` equals `ENNReal.ofReal (π_θ(u | x))`
whenever the state density at `x` is positive and finite.

The factorization does not follow from `StochasticMDP` alone (Radon–Nikodym derivatives are unique
only a.e.); supply it when the chosen versions agree with the density policy (e.g.
continuous densities), or derive it from the `stageK` disintegration in a dedicated lemma.
-/
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
  ℙ[M.traj θ]((a t) = aₜ | (s t) = sₜ) = ENNReal.ofReal (M.π[θ] sₜ aₜ) := by
-- proof
  intro hP
  change (M.traj θ).prob (a t, s t) (aₜ, sₜ) /
      ((M.traj θ).map (fun ω ↦ ((a t, s t) ω).2)).rnDeriv ReferenceMeasure.measure sₜ =
    ENNReal.ofReal (M.π[θ] sₜ aₜ)
  have hsnd : (fun ω ↦ ((a t, s t) ω).2) = s t := rfl
  rw [hsnd, h₂, ENNReal.mul_div_cancel_right h₃ h₄]


-- created on 2026-10-21
-- updated on 2026-11-16