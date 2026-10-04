import Mathlib.Probability.Independence.Conditional
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.All_Imp_EqProbSCond.of.CondIndep
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import sympy.stats.joint_rv
open ProbabilityTheory MeasureTheory Measure Random


/--
Conditional independence `x ⟂ y | z` of discrete random variables (counting reference measures)
in terms of the measures of the events:
`π {x = u, y = v, z = w} * π {z = w} = π {x = u, z = w} * π {y = v, z = w}`,
i.e. `ℙ(x = u, y = v | z = w) = ℙ(x = u | z = w) * ℙ(y = v | z = w)` with the denominators cleared,
so no non-vanishing assumption is needed.
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  [StandardBorelSpace α] [Nonempty α] [Countable α] [MeasurableSingletonClass α]
  [StandardBorelSpace β] [Nonempty β] [Countable β] [MeasurableSingletonClass β]
  [Countable γ] [MeasurableSingletonClass γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count)
  (hγ : ReferenceMeasure.measure (α := γ) = Measure.count)
  (hCI : x ⟂ᵢ[π] y | z)
  (u : α)
  (v : β)
  (w : γ) :
-- imply
  π (x ⁻¹' {u} ∩ y ⁻¹' {v} ∩ z ⁻¹' {w}) * π (z ⁻¹' {w}) =
    π (x ⁻¹' {u} ∩ z ⁻¹' {w}) * π (y ⁻¹' {v} ∩ z ⁻¹' {w}) := by
-- proof
  have hβγ : ReferenceMeasure.measure (α := β × γ) = Measure.count := by
    change (ReferenceMeasure.measure (α := β)).prod ReferenceMeasure.measure = Measure.count
    rw [hβ, hγ, ← Count.eq.ProdCountS]
  have hαβγ : ReferenceMeasure.measure (α := α × (β × γ)) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod ReferenceMeasure.measure = Measure.count
    rw [hα, hβγ, ← Count.eq.ProdCountS]
  have hαγ : ReferenceMeasure.measure (α := α × γ) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod ReferenceMeasure.measure = Measure.count
    rw [hα, hγ, ← Count.eq.ProdCountS]
  have hPxyz : SinglePSpace π (x, y, z) :=
    SinglePSpace.of.EqMeasureCount.Measurable (hx.prodMk (hy.prodMk hz)) hαβγ
  have hPyz : SinglePSpace π (y, z) :=
    SinglePSpace.of.EqMeasureCount.Measurable (hy.prodMk hz) hβγ
  have hPxz : SinglePSpace π (x, z) :=
    SinglePSpace.of.EqMeasureCount.Measurable (hx.prodMk hz) hαγ
  have h := All_Imp_EqProbSCond.of.CondIndep hx hy hz hPxyz hCI
  simp only [hα, hβ, hγ, ae_count_iff] at h
  have h := h u v w
  have e₁ : ((y, z)) ⁻¹' {(v, w)} = y ⁻¹' {v} ∩ z ⁻¹' {w} := by
    ext ω
    simp [JointRandomSymbol, Prod.ext_iff]
  rw [Prob.eq.Measure.of.Eq_Count hβγ, ProbCond.eq.Div.of.Eq_Count.Eq_Count hα hβγ,
    ProbCond.eq.Div.of.Eq_Count.Eq_Count hα hγ, e₁, ← Set.inter_assoc] at h
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