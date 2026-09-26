import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Law of total expectation for a random variable `X` with finitely many values:
`𝔼[𝔼[Y | X]] = 𝔼[Y]`, where the outer expectation is the finite sum over the values of `X`
weighted by `ℙ(X = x)` and `𝔼[Y | X = x]` is the integral against `μ[| X ⁻¹' {x}]`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → α}
  {Y : Ω → ℝ}
-- given
  (h₀ : Measurable X)
  (h₁ : Integrable Y μ) :
-- imply
  ∑ x, (μ (X ⁻¹' {x})).toReal * ∫ ω, Y ω ∂μ[|X ⁻¹' {x}] = ∫ ω, Y ω ∂μ := by
-- proof
  have h₂ : ∀ x, (μ (X ⁻¹' {x})).toReal * ∫ ω, Y ω ∂μ[|X ⁻¹' {x}] = ∫ ω in X ⁻¹' {x}, Y ω ∂μ := by
    intro x
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.toReal_inv]
    by_cases hx : μ (X ⁻¹' {x}) = 0
    · rw [Measure.restrict_eq_zero.mpr hx]
      simp
    · rw [mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hx, measure_ne_top μ _⟩), one_mul]
  simp_rw [h₂]
  rw [← integral_iUnion_fintype (fun x => h₀ (measurableSet_singleton x))
    (fun x y hxy => Set.disjoint_left.mpr fun ω h₃ h₄ => hxy (h₃.symm.trans h₄))
    (fun x => h₁.integrableOn)]
  have h₅ : (⋃ x, X ⁻¹' {x}) = Set.univ := by
    ext ω; simp
  rw [h₅, Measure.restrict_univ]


-- created on 2026-09-26
