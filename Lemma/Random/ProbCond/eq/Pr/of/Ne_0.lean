import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Measurable_S
import Lemma.Random.RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
In the trajectory model the conditional law of the action `a[t]` given the state `s[t] = x` is the policy:
`Pr(a[t] = u | s[t] = x) = Pr[a:π](a[t] = u | s[t] = x)` whenever `s[t] = x` has positive probability.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {t : ℕ}
  {x : S}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : A) :
-- imply
  ((M θ)[|s t ⁻¹' {x}]).real (a t ⁻¹' {u}) = M.Pr θ x u := by
-- proof
  classical
  rw [measureReal_def, cond_apply (Random.Measurable_S h₁ t (measurableSet_singleton x)), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb h₁, inv_mul_cancel_left₀ h₂]
  rfl


-- created on 2026-09-26
