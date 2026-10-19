import Lemma.Random.RealInterPreimage_Preimage.eq.MulRealPreimageProb.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Joint law of state and action in the trajectory model:
`Pr(s[t] = x, a[t] = u) = Pr(s[t] = x) * Pr[a:π](a[t] = u | s[t] = x)`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {t : ℕ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (x : S)
  (u : A) :
-- imply
  (M θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) = (M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u := by
-- proof
  classical
  apply RealInterPreimage_Preimage.eq.MulRealPreimageProb.of.All_Eq (M := M) h₀ θ t x u


-- created on 2026-09-26
