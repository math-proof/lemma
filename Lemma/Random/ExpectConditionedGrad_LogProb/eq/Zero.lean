import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import sympy.Basic
import Lemma.Random.ProbCond.eq.Pr.of.Ne_0
import Lemma.Random.Eq_0.of.EqReal_0
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Expected grad-log-prob lemma on a finite outcome space: for a differentiable, positive family of
probability vectors `p θ` (e.g. the policy `π_θ(· | s)`),
`𝔼_{a ∼ p θ}[∇_θ log p θ a] = ∑ a, p θ a • ∇_θ log p θ a = 0`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [Fintype A]
  {p : Θ → A → ℝ}
  {θ : Θ}
-- given
  (h₀ : ∀ θ', ∑ a, p θ' a = 1)
  (h₁ : ∀ a, p θ a > 0)
  (h₂ : ∀ a, DifferentiableAt ℝ (fun θ' => p θ' a) θ) :
-- imply
  ∑ a, p θ a • fderiv ℝ (fun θ' => Real.log (p θ' a)) θ = 0 := by
-- proof
  have h₃ : ∀ a, fderiv ℝ (fun θ' => Real.log (p θ' a)) θ =
      (p θ a)⁻¹ • fderiv ℝ (fun θ' => p θ' a) θ :=
    fun a => ((h₂ a).hasFDerivAt.log (h₁ a).ne').fderiv
  simp_rw [h₃, smul_smul]
  have h₄ : ∀ a, p θ a * (p θ a)⁻¹ = 1 := fun a => mul_inv_cancel₀ (h₁ a).ne'
  simp only [h₄, one_smul]
  have h₅ : HasFDerivAt (fun θ' => ∑ a, p θ' a) (∑ a, fderiv ℝ (fun θ' => p θ' a) θ) θ :=
    HasFDerivAt.fun_sum fun a _ => (h₂ a).hasFDerivAt
  have h₆ : (fun θ' => ∑ a, p θ' a) = fun _ => (1 : ℝ) := funext h₀
  rw [h₆] at h₅
  exact h₅.unique (hasFDerivAt_const 1 θ)

/--
Expected grad-log-prob lemma for the policy of the trajectory model, conditioned on the state:
`𝔼[∇_θ log π_θ(a[t] | s[t]) | s[t] = x] = 0` for a positive policy differentiable at `θ`.
-/
@[path]
private lemma policy
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
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : ∀ u, M.policy.prob θ x u > 0)
  (h₂ : ∀ u, DifferentiableAt ℝ (fun θ' => M.policy.prob θ' x u) θ) :
-- imply
  ∫ ω, fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x (a t ω))) θ ∂(M θ)[|s t ⁻¹' {x}] = 0 := by
-- proof
  if hP : M θ (s t ⁻¹' {x}) = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hP]
  else
    have := cond_isProbabilityMeasure (μ := M θ) hP
    have hP' : (M θ).real (s t ⁻¹' {x}) ≠ 0 := fun h => hP (Eq_0.of.EqReal_0 (M := M) θ h)
    let φ : A → (Θ →L[ℝ] ℝ) := fun u => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x u)) θ
    have h₃ : ∫ ω, φ (a t ω) ∂(M θ)[|s t ⁻¹' {x}] =
        ∫ u, φ u ∂((M θ)[|s t ⁻¹' {x}].map (a t)) :=
      (integral_map (Random.Measurable.of.All_Eq.snd.snd h₀ t).aemeasurable StronglyMeasurable.of_discrete.aestronglyMeasurable).symm
    have h₄ : ∀ u, ((M θ)[|s t ⁻¹' {x}].map (a t)).real {u} = M.policy.prob θ x u := by
      intro u
      rw [measureReal_def, Measure.map_apply (Random.Measurable.of.All_Eq.snd.snd h₀ t) (measurableSet_singleton u), ← measureReal_def]
      apply ProbCond.eq.Pr.of.Ne_0 h₀ hP' u
    show ∫ ω, φ (a t ω) ∂(M θ)[|s t ⁻¹' {x}] = 0
    rw [h₃, integral_fintype Integrable.of_finite]
    simp_rw [h₄]
    apply main (p := fun θ' u => M.policy.prob θ' x u)
      (fun θ' => M.policy.sum_eq_one θ' x) h₁ h₂


-- created on 2026-10-20
