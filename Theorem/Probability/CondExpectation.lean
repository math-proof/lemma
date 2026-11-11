import Syntax.Probability.Expectation.Elab
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


/-- If the atom `{y = y0}` has positive mass, `condEval` agrees with the elementary event form. -/
theorem Expectation.condEval_eq_condEvent
    {Ω α γ β : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [Expectation β]
    {π : Measure Ω} [IsFiniteMeasure π]
    {x : Ω → α} {y : Ω → γ} {f : α → β} {y0 : γ}
    (hx : Measurable x) (hy : Measurable y) (hpos : π.map y {y0} ≠ 0) :
    Expectation.condEval π x y f y0 = Expectation.condEvent π x y f y0 := by
  unfold Expectation.condEval Expectation.condEvent
  refine congrArg (fun μ => expectation μ f) ?_
  ext s hs
  have hy0 : MeasurableSet ({y0} : Set γ) := measurableSet_singleton y0
  have hpre : MeasurableSet (y ⁻¹' ({y0} : Set γ)) := hy hy0
  rw [ProbabilityTheory.condDistrib_apply_of_ne_zero (hX := hy) (hY := hx) y0 hpos s]
  rw [Measure.map_apply hx hs, ProbabilityTheory.cond_apply hpre]
  have hprod : MeasurableSet (({y0} : Set γ) ×ˢ s) := hy0.prod hs
  rw [Measure.map_apply (hy.prodMk hx) hprod, Measure.map_apply hy hy0]
  have hset :
      (fun a ↦ (y a, x a)) ⁻¹' (({y0} : Set γ) ×ˢ s) =
        y ⁻¹' ({y0} : Set γ) ∩ x ⁻¹' s := by
    ext ω
    simp [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, Set.mem_singleton_iff]
  rw [hset]


/-- `condEval` composed with `y` is a version of the σ-algebra conditional `condSigma`. -/
theorem Expectation.condEval_comp_ae_eq_condSigma
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace γ]
    {π : Measure Ω} [IsFiniteMeasure π]
    {x : Ω → α} {y : Ω → γ} {f : α → ℝ}
    (hx : AEMeasurable x π) (hy : Measurable y)
    (hf : StronglyMeasurable f) (hint : Integrable (fun ω => f (x ω)) π) :
    (fun ω => Expectation.condEval π x y f (y ω)) =ᵐ[π]
      Expectation.condSigma π x y f := by
  unfold Expectation.condEval Expectation.condSigma
  have h :=
    ProbabilityTheory.condExp_ae_eq_integral_condDistrib
      (μ := π) (X := y) (Y := x) (f := f) hy hx hf hint
  filter_upwards [h] with ω hω
  rw [expectation_real]
  exact hω.symm


/-- If the atom `{y = y0}` has positive mass, `𝔼[… | y = y0]` is the Bochner integral
against the elementary conditional measure `π[|y ⁻¹' {y0}]`. -/
theorem Expectation.condEval_eq_integral
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {π : Measure Ω} [IsFiniteMeasure π]
    {x : Ω → α} {y : Ω → γ} {f : α → ℝ} {y0 : γ}
    (hx : Measurable x) (hy : Measurable y) (hf : Measurable f)
    (hpos : π.map y {y0} ≠ 0) :
    Expectation.condEval π x y f y0 = ∫ ω, f (x ω) ∂(π[|y ⁻¹' {y0}]) := by
  rw [Expectation.condEval_eq_condEvent hx hy hpos]
  exact Expectation.condEvent_eq_integral hx.aemeasurable hf

