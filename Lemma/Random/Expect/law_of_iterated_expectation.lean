import Lemma.Random.Expect.law_of_total_expectation
open MeasureTheory ProbabilityTheory


/--
Law of iterated expectations over two finite-valued random variables `Y`, `Z`:
`𝔼[f] = 𝔼_{Y, Z}[𝔼[f | Y, Z]]`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {Y : Ω → α} {Z : Ω → β}
  {f : Ω → ℝ}
-- given
  (h₀ : Measurable Y)
  (h₁ : Measurable Z)
  (h₂ : Integrable f μ) :
-- imply
  ∫ ω, f ω ∂μ = ∑ y, ∑ z, (μ (Y ⁻¹' {y} ∩ Z ⁻¹' {z})).toReal * ∫ ω, f ω ∂μ[|Y ⁻¹' {y} ∩ Z ⁻¹' {z}] := by
-- proof
  have h₃ := Random.Expect.law_of_total_expectation (X := fun ω => (Y ω, Z ω)) (h₀.prodMk h₁) h₂
  rw [← h₃, Fintype.sum_prod_type]
  congr 1
  funext y
  congr 1
  funext z
  have h₄ : (fun ω => (Y ω, Z ω)) ⁻¹' {(y, z)} = Y ⁻¹' {y} ∩ Z ⁻¹' {z} := by
    ext ω; simp
  rw [h₄]


-- created on 2026-09-26
