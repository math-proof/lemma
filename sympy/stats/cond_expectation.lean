import sympy.stats.joint_rv
open MeasureTheory ProbabilityTheory

/-- `𝔼[… | y = y0]` against a conditional law is the Bochner integral against `π[|y ⁻¹' {y0}]`. -/
theorem Expectation.condEvent_eq_integral
    {Ω α γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {π : Measure Ω} {x : Ω → α} {y : Ω → γ} {f : α → ℝ} {y0 : γ}
    (hx : AEMeasurable x π) (hf : Measurable f) :
    Expectation.condEvent π x y f y0 = ∫ ω, f (x ω) ∂(π[|y ⁻¹' {y0}]) := by
  unfold Expectation.condEvent
  rw [expectation_real]
  exact integral_map (hx.mono_ac (ProbabilityTheory.cond_absolutelyContinuous)) hf.aestronglyMeasurable
