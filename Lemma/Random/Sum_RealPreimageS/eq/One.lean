import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Integral.eq.Sum_SMul
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
The state marginal sums to `1`: `∑ y, Pr(s[t] = y) = 1`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∑ y, (M θ).real (s t ⁻¹' {y}) = 1 := by
-- proof
  have h := Random.Integral.eq.Sum_SMul h₁ (M := M) θ t (fun _ => (1:ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h.symm


-- created on 2026-10-06
