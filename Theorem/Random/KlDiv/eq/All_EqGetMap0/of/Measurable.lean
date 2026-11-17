module

public import Theorem.ENNReal.KlDiv.eq.All_Eq_0
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.ProbabilityMassFunction.Basic

public section

open ENNReal InformationTheory MeasureTheory Real


public theorem kl_map [MeasurableSpace α] [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : α → β} (hφ : Measurable φ) :
  klDiv (ν.map φ) (μ.map φ) = if ∀ a, (μ.map φ) {a} = 0 → (ν.map φ) {a} = 0 then ENNReal.ofReal (∑ a, ((ν.map φ) {a}).toReal * log (((ν.map φ) {a}).toReal / ((μ.map φ) {a}).toReal)) else ⊤ := by
  let : IsProbabilityMeasure (μ.map φ) := (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (ν.map φ) := (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  have hμ : (μ.map φ).toPMF.toMeasure = μ.map φ := Measure.toPMF_toMeasure (μ.map φ)
  have hν : (ν.map φ).toPMF.toMeasure = ν.map φ := Measure.toPMF_toMeasure (ν.map φ)
  conv_lhs => rw [← hν, ← hμ]
  rw [KlDiv.eq.All_Eq_0 (μ.map φ).toPMF (ν.map φ).toPMF]
  rfl

/--
Pushing two probability measures forward by a finite measurable map turns their Kullback–Leibler
divergence into the explicit entropy of the cell masses. The divergence is `⊤` when the first
measure charges a cell that the second misses. This is the rate in the partition form of Sanov's
theorem.
-/
public theorem Random.KlDiv.eq.All_EqGetMap0.of.Measurable
  [MeasurableSpace α]
  [Fintype β] [DecidableEq β]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {φ : α → β}
-- given
  (hφ : Measurable φ) :
-- imply
  klDiv (ν.map φ) (μ.map φ) = if ∀ a, (μ.map φ) {a} = 0 → (ν.map φ) {a} = 0 then ENNReal.ofReal (∑ a, ((ν.map φ) {a}).toReal * log (((ν.map φ) {a}).toReal / ((μ.map φ) {a}).toReal)) else ⊤ :=
-- proof
  kl_map hφ


-- created on 2026-11-02
