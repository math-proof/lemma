import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory


/--
Continuous-action bridge between the `ℙ` binder sugar and a density policy:
given absolute continuity of `law(a[t], s[t])` (so `SinglePSpace` elaborates) and a
pointwise factorization of the joint density into policy dens × state RN derivative,
the conditional density `ℙ[M θ](a[t] = u | s[t] = x)` equals `ENNReal.ofReal (π_θ(u | x))`
whenever the state density at `x` is positive and finite.

The factorization does not follow from `Env` alone (Radon–Nikodym derivatives are unique
only a.e.); supply it when the chosen versions agree with the density policy (e.g.
continuous densities), or derive it from the `stageK` disintegration in a dedicated lemma.
-/
@[path]
private lemma main
  [ReferenceMeasure 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ} {t : ℕ} {x : 𝒮} {u : 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : DensityModel.IsPolicyTrajectory M r s a)
  (h₁ : DensityModel.AbsContJointAS M a s)
  (h₂ : (M θ).prob (a t, s t) (u, x) =
    ENNReal.ofReal (M.policy.prob θ x u) *
      ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure 𝒮) x)
  (h₃ : ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure 𝒮) x ≠ 0)
  (h₄ : ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure 𝒮) x ≠ ⊤) :
-- imply
  have : SinglePSpace (M θ) (a t, s t) := h₀.singlePSpace_as (haj := h₁) θ t
  ℙ[M θ]((a t) = u | (s t) = x) = ENNReal.ofReal (M.policy.prob θ x u) := by
-- proof
  intro hP
  change (M θ).prob (a t, s t) (u, x) /
      ((M θ).map (fun ω ↦ ((a t, s t) ω).2)).rnDeriv ReferenceMeasure.measure x =
    ENNReal.ofReal (M.policy.prob θ x u)
  have hsnd : (fun ω ↦ ((a t, s t) ω).2) = s t := rfl
  rw [hsnd, h₂, ENNReal.mul_div_cancel_right h₃ h₄]


-- created on 2026-10-21
