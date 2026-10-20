import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
A conditional probability is a probability: summing the conditional masses of a finite observable gives `1`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {Y : Ω → β} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  {s : Set Ω}
-- given
  (h₀ : π s ≠ 0)
  (h₁ : Measurable Y) :
-- imply
  ∑ y, (π[|s]).real (Y ⁻¹' {y}) = 1 := by
-- proof
  have : IsProbabilityMeasure (π[|s]) := cond_isProbabilityMeasure h₀
  classical
  have hdisj : Pairwise fun y z : β => Disjoint (Y ⁻¹' {y}) (Y ⁻¹' {z}) := by
    intro y z hyz
    rw [Set.disjoint_left]
    intro ω hy hz
    apply hyz (hy.symm.trans hz)
  have hsum : ∑ y, (π[|s]) (Y ⁻¹' {y}) = 1 := by
    rw [← measure_biUnion_finset
      (fun y _ z _ hyz => hdisj (i := y) (j := z) hyz)
      (fun y _ => h₁ (measurableSet_singleton y))]
    rw [show (⋃ y ∈ Finset.univ, Y ⁻¹' {y}) = Set.univ by ext ω; simp]
    apply measure_univ
  have hreal : ∑ y, ((π[|s]) (Y ⁻¹' {y})).toReal =
      (∑ y, (π[|s]) (Y ⁻¹' {y})).toReal := by
    rw [ENNReal.toReal_sum (fun y _ => measure_ne_top _ _)]
  simpa [measureReal_def, hsum] using hreal


-- created on 2023-04-03
-- updated on 2026-10-17
