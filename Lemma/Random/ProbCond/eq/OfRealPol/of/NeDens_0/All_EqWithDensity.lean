import sympy.stats.policy_trajectory.continuous_action
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
  [ReferenceMeasure S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ} {t : ℕ} {x : S} {u : A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : DensityModel.IsPolicyTrajectory M r s a)
  (h₁ : DensityModel.AbsContJointAS M a s)
  (h₂ : (M θ).prob (a t, s t) (u, x) =
    ENNReal.ofReal (M.policy.prob θ x u) *
      ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x)
  (h₃ : ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x ≠ 0)
  (h₄ : ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x ≠ ⊤) :
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
