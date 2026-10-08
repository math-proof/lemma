import Lemma.Random.ProbCond.eq.Pr.of.Ne_0
import Lemma.Random.Expect_ConditionedGrad_LogProb.eq.Zero
import Lemma.Random.Eq_0.of.EqReal_0
import Lemma.Random.Measurable_A
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Expected grad-log-prob lemma for the policy of the trajectory model, conditioned on the state:
`𝔼[∇_θ log π_θ(a[t] | s[t]) | s[t] = x] = 0` for a positive policy differentiable at `θ`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
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
  (h₂ : ∀ u, M.pol.prob θ x u > 0)
  (h₃ : ∀ u, DifferentiableAt ℝ (fun θ' => M.pol.prob θ' x u) θ) :
-- imply
  ∫ ω, fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x (a t ω))) θ ∂(M θ)[|s t ⁻¹' {x}] = 0 := by
-- proof
  by_cases hP : M θ (s t ⁻¹' {x}) = 0
  · simp [cond_eq_zero_of_meas_eq_zero hP]
  · have := cond_isProbabilityMeasure (μ := M θ) hP
    have hP' : (M θ).real (s t ⁻¹' {x}) ≠ 0 := fun h => hP (Eq_0.of.EqReal_0 (M := M) θ h)
    let φ : A → (Θ →L[ℝ] ℝ) := fun u => fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x u)) θ
    have h₄ : ∫ ω, φ (a t ω) ∂(M θ)[|s t ⁻¹' {x}] =
        ∫ u, φ u ∂(((M θ)[|s t ⁻¹' {x}]).map (a t)) :=
      (integral_map (Random.Measurable_A h₁ t).aemeasurable StronglyMeasurable.of_discrete.aestronglyMeasurable).symm
    have h₅ : ∀ u, (((M θ)[|s t ⁻¹' {x}]).map (a t)).real {u} = M.pol.prob θ x u := by
      intro u
      rw [measureReal_def, Measure.map_apply (Random.Measurable_A h₁ t) (measurableSet_singleton u), ← measureReal_def]
      exact ProbCond.eq.Pr.of.Ne_0 h₁ hP' u
    show ∫ ω, φ (a t ω) ∂(M θ)[|s t ⁻¹' {x}] = 0
    rw [h₄, integral_fintype Integrable.of_finite]
    simp_rw [h₅]
    exact Expect_ConditionedGrad_LogProb.eq.Zero (p := fun θ' u => M.pol.prob θ' x u)
      (fun θ' => M.pol.sum_eq_one θ' x) h₂ h₃


-- created on 2023-04-03
