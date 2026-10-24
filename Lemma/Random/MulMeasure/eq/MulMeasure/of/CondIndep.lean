import Mathlib.Probability.Independence.Conditional
import Lemma.Random.All_Imp_EqProbSCond.of.CondIndep
import Lemma.Random.SinglePSpace.of.Measurable
import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
open ProbabilityTheory MeasureTheory Measure Random


/--
Conditional independence `x ⟂ y | z` of discrete random variables (counting reference measures)
in terms of the measures of the events:
`π {x = u, y = v, z = w} * π {z = w} = π {x = u, z = w} * π {y = v, z = w}`,
i.e. `ℙ(x = u, y = v | z = w) = ℙ(x = u | z = w) * ℙ(y = v | z = w)` with the denominators cleared,
so no non-vanishing assumption is needed.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure α] [CountableMeasure β] [CountableMeasure γ]
  [StandardBorelSpace α] [Nonempty α] [Countable α] [MeasurableSingletonClass α]
  [StandardBorelSpace β] [Nonempty β] [Countable β] [MeasurableSingletonClass β]
  [Countable γ] [MeasurableSingletonClass γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
  (hCI : x ⟂ᵢ[π] y | z)
  (u : α)
  (v : β)
  (w : γ) :
-- imply
  π (x ⁻¹' {u} ∩ y ⁻¹' {v} ∩ z ⁻¹' {w}) * π (z ⁻¹' {w}) =
    π (x ⁻¹' {u} ∩ z ⁻¹' {w}) * π (y ⁻¹' {v} ∩ z ⁻¹' {w}) := by
-- proof
  have hα : ReferenceMeasure.measure (α := α) = Measure.count :=
    CountableMeasure.measure_eq_count
  have hβ : ReferenceMeasure.measure (α := β) = Measure.count :=
    CountableMeasure.measure_eq_count
  have hγ : ReferenceMeasure.measure (α := γ) = Measure.count :=
    CountableMeasure.measure_eq_count
  have hPxyz : SinglePSpace π (x, y, z) :=
    SinglePSpace.of.Measurable (hx.prodMk (hy.prodMk hz))
  have hPyz : SinglePSpace π (y, z) :=
    SinglePSpace.of.Measurable (hy.prodMk hz)
  have hPxz : SinglePSpace π (x, z) :=
    SinglePSpace.of.Measurable (hx.prodMk hz)
  have h := All_Imp_EqProbSCond.of.CondIndep hx hy hz hPxyz hCI
  simp only [hα, hβ, hγ, ae_count_iff] at h
  have h := h u v w
  have e₁ : ((y, z)) ⁻¹' {(v, w)} = y ⁻¹' {v} ∩ z ⁻¹' {w} := by
    ext ω
    simp [JointRandomSymbol, Prod.ext_iff]
  have hdiv₁ :
    ℙ[π](x = u | (y, z) = (v, w)) =
      π (x ⁻¹' {u} ∩ (y, z) ⁻¹' {(v, w)}) / π ((y, z) ⁻¹' {(v, w)}) := by
    have : SinglePSpace π (x, show Ω → β × γ from (y, z)) :=
      SinglePSpace.of.Measurable (hx.prodMk (hy.prodMk hz))
    exact ProbCond.eq.Div.of.SinglePSpace inferInstance u (v, w)
  have hdiv₂ :
    ℙ[π](x = u | z = w) = π (x ⁻¹' {u} ∩ z ⁻¹' {w}) / π (z ⁻¹' {w}) := by
    have := hPxz
    exact ProbCond.eq.Div.of.SinglePSpace inferInstance u w
  rw [EqProb, hdiv₁, hdiv₂, e₁, ← Set.inter_assoc] at h
  if hB : π (y ⁻¹' {v} ∩ z ⁻¹' {w}) = 0 then
    have hT : π (x ⁻¹' {u} ∩ y ⁻¹' {v} ∩ z ⁻¹' {w}) = 0 := by
      apply measure_mono_null _ hB
      intro ω hω
      exact ⟨hω.1.2, hω.2⟩
    rw [hT, hB]
    simp
  else
    have h := h hB
    have hZ : π (z ⁻¹' {w}) ≠ 0 := by
      intro h₀
      apply hB
      apply measure_mono_null _ h₀
      intro ω hω
      exact hω.2
    rw [ENNReal.div_eq_div_iff hZ (measure_ne_top _ _) hB (measure_ne_top _ _)] at h
    rw [mul_comm, h, mul_comm]


-- created on 2026-10-02
-- updated on 2026-10-23
