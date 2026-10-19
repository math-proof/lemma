import sympy.stats.policy_trajectory
import sympy.stats.cond_expectation
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The conditional expectation form of `V` is the Bochner integral of the discounted return
against the conditional measure `(M θ)[| s t ⁻¹' {x}]`.
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
  (x : S) :
-- imply
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x}] := by
-- proof
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  simp only [Expectation.asRV_process]
  apply Expectation.condEvent_eq_integral h₀.aemeasurable hfG


-- created on 2026-10-11
