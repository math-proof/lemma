import Syntax.Probability.Expectation.Elab
import Lemma.Random.Map.eq.WithDensityProb
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Theorem.Probability.JointRv.AsRV
open MeasureTheory Finset Random


/--
Finite importance-sampling variance gap. With likelihood ratio `ℙ[π](x) / ℙ[π'](x)`,
`𝔼[x:π](f(x)² * (1 - ℙ[π](x) / ℙ[π'](x))) = 𝕍𝕒𝕣[x:π](f x) - 𝕍𝕒𝕣[x:π'](f x * ℙ[π](x) / ℙ[π'](x))`.
The squared means cancel because `𝔼[x:π'](f(x) * ℙ[π](x) / ℙ[π'](x)) = 𝔼[x:π](f x)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α] [Fintype α] [MeasurableSingletonClass α]
  {x : Ω → α} {f : α → ℝ}
  {π : Measure Ω} [SinglePSpace π x]
  {π' : Measure Ω} [SinglePSpace π' x]
-- given
  (h₀ : ∀ a, ℙ[π'](x = a) ≠ 0) :
-- imply
  𝔼[x: π](f x ^ 2 * (1 - (ℙ[π](x)).toReal / (ℙ[π'](x)).toReal)) =
    𝕍𝕒𝕣[x: π](f x) -
      𝕍𝕒𝕣[x: π'](f x * ((ℙ[π](x)).toReal / (ℙ[π'](x)).toReal)) := by
-- proof
  have hμ : (ReferenceMeasure.measure : Measure α) = Measure.count :=
    CountableMeasure.measure_eq_count
  have htop (ρ : Measure Ω) [SinglePSpace ρ x] : ∀ a, ρ.prob x a ≠ ⊤ := by
    intro a
    simp only [Measure.prob, hμ]
    exact Measure.ae_count_iff.mp (Measure.rnDeriv_ne_top (ρ.map x) Measure.count) a
  have hE (ρ : Measure Ω) [SinglePSpace ρ x] (g : α → ℝ) :
    𝔼[x: ρ](g x) = ∑ a, g a * (ρ.prob x a).toReal := by
    simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
    rw [Map.eq.WithDensityProb (π := ρ) (x := x), hμ]
    have hden : ρ.prob x = (ρ.map x).rnDeriv Measure.count := by
      simp [Measure.prob]
    rw [hden]
    rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.ae_count_iff.mpr fun a =>
        lt_top_iff_ne_top.mpr (by simpa [hden] using htop ρ a))]
    simp [integral_count, smul_eq_mul, mul_comm]
  have hmass (ρ : Measure Ω) [SinglePSpace ρ x] : ∑ a, (ρ.prob x a).toReal = 1 := by
    have : IsProbabilityMeasure (ρ.map x) := inferInstance
    have h := hE ρ (fun _ => (1 : ℝ))
    simpa [Expectation.asRV_function, Expectation.ofRV, expectation_real, integral_const,
      measureReal_def, IsProbabilityMeasure.measure_univ] using h.symm
  have hDev (ρ : Measure Ω) [SinglePSpace ρ x] (g : α → ℝ) :
    ∑ a, (g a - ∑ b, g b * (ρ.prob x b).toReal) ^ 2 * (ρ.prob x a).toReal =
      ∑ a, g a ^ 2 * (ρ.prob x a).toReal - (∑ a, g a * (ρ.prob x a).toReal) ^ 2 := by
    set μ : α → ℝ := fun a => (ρ.prob x a).toReal
    set m : ℝ := ∑ b, g b * μ b
    have hm : ∑ a, μ a = 1 := by simpa [μ] using hmass ρ
    have hring : ∑ a, (g a - m) ^ 2 * μ a =
        ∑ a, (g a ^ 2 * μ a - 2 * m * (g a * μ a) + m ^ 2 * μ a) := by
      refine sum_congr rfl fun a _ => ?_
      ring
    rw [hring, sum_add_distrib, sum_sub_distrib]
    simp only [← mul_sum, hm]
    ring
  have hVar (ρ : Measure Ω) [SinglePSpace ρ x] (g : α → ℝ) :
    𝕍𝕒𝕣[x: ρ](g x) =
      ∑ a, g a ^ 2 * (ρ.prob x a).toReal - (∑ a, g a * (ρ.prob x a).toReal) ^ 2 := by
    have hsq := hE ρ (fun a => (g a - 𝔼[x: ρ](g x)) ^ 2)
    rw [hsq, hE ρ g]
    exact hDev ρ g
  set μ : α → ℝ := fun a => (π.prob x a).toReal
  set ν : α → ℝ := fun a => (π'.prob x a).toReal
  have hν : ∀ a, ν a ≠ 0 := fun a => by
    have hne : π'.prob x a ≠ 0 := h₀ a
    have hfin : π'.prob x a ≠ ⊤ := htop π' a
    simpa [ν, ENNReal.toReal_eq_zero_iff, not_or] using And.intro hne hfin
  have hmean : ∑ a, f a * (μ a / ν a) * ν a = ∑ a, f a * μ a := by
    refine sum_congr rfl fun a _ => ?_
    field_simp [hν a]
  have hsqμ : ∑ a, (f a * (μ a / ν a)) ^ 2 * ν a = ∑ a, f a ^ 2 * (μ a / ν a) * μ a := by
    refine sum_congr rfl fun a _ => ?_
    field_simp [hν a]
  have hlhs : ∑ a, f a ^ 2 * (1 - μ a / ν a) * μ a =
      ∑ a, f a ^ 2 * μ a - ∑ a, f a ^ 2 * (μ a / ν a) * μ a := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    field_simp [hν a]
  have hL := hE π (fun a => f a ^ 2 * (1 - (π.prob x a).toReal / (π'.prob x a).toReal))
  have hV := hVar π f
  have hV' := hVar π' (fun a => f a * ((π.prob x a).toReal / (π'.prob x a).toReal))
  simp only [μ, ν] at hmean hsqμ hlhs
  rw [hL, hV, hV', hmean, hsqμ, hlhs]
  ring


-- created on 2023-03-24
-- updated on 2026-11-12
