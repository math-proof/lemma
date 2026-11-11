import Theorem.Dynamics.PolicyTrajectory
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The observation form of `V` agrees with the Bochner integral of the discounted return
against the conditional measure `(M θ)[| s t ⁻¹' {x}]`, on atoms of positive mass.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
-- given
  (h₀ : Measurable (fun ω t ↦ r t ω))
  (θ : Θ)
  (γ : ℝ)
  (t : ℕ)
  (x : S)
  (hs : Measurable (s t))
  (hx : (M θ) (s t ⁻¹' {x}) ≠ 0) :
-- imply
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x}] := by
-- proof
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hpos : (M θ).map (s t) {x} ≠ 0 := by
    rwa [Measure.map_apply hs (measurableSet_singleton x)]
  simp only [Expectation.asRV_process]
  exact Expectation.condEval_eq_integral h₀ hs hfG hpos


-- created on 2026-10-11
-- updated on 2026-11-11
