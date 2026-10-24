/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/PaleyZygmund.lean -/


import Lemma.Measure.PaleyZygmund


open MeasureTheory

/-- The backported theorem exposes the exact upstream API and namespace. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ_nn : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ) * μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} :=
  ProbabilityTheory.paley_zygmund hZ_nn hZ2 hθ0 hθ1

/-- The stronger upstream API directly recovers the former Wanted signature. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hX_meas : Measurable X)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (_hX_int : Integrable X μ)
    (hX2_int : Integrable (fun ω => (X ω) ^ 2) μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 ≤
      μ.real {ω | θ * ∫ ω, X ω ∂μ < X ω} *
        ∫ ω, (X ω) ^ 2 ∂μ := by
  have hX2 : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hX2_int
  simpa [mul_comm] using
    (ProbabilityTheory.paley_zygmund (μ := μ) (Z := X)
      (ae_of_all μ hX_nonneg) hX2 hθ0 hθ1)
