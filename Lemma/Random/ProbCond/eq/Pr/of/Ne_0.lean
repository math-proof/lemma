import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.RealInterPreimage_Preimage.eq.MulRealPreimageProb.of.All_Eq
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
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : A) :
-- imply
  ((M θ)[|s t ⁻¹' {x}]).real (a t ⁻¹' {u}) = M.pol.prob θ x u := by
-- proof
  classical
  rw [measureReal_def, cond_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, RealInterPreimage_Preimage.eq.MulRealPreimageProb.of.All_Eq h₀, inv_mul_cancel_left₀ h₁]


-- created on 2026-09-26
