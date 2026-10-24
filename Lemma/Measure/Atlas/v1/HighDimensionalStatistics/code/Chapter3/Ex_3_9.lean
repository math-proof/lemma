import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Ex_3_9
open MeasureTheory Set intervalIntegral Filter Chapter3


namespace Chapter3

/--
[haarMother_stronglyMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Ex_3_9.lean)
-/
@[path]
lemma haarMother_stronglyMeasurable
-- imply
  StronglyMeasurable haarMother := by
-- proof
  unfold haarMother
  exact StronglyMeasurable.ite (measurableSet_Ici.inter measurableSet_Iio)
    stronglyMeasurable_const (StronglyMeasurable.ite
      (measurableSet_Ici.inter measurableSet_Iic)
      stronglyMeasurable_const stronglyMeasurable_const)

end Chapter3

namespace Chapter3

/--
[haarMother_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Ex_3_9.lean)
-/
@[path]
lemma haarMother_intervalIntegrable
  {a b : ℝ} :
-- imply
  IntervalIntegrable haarMother volume a b := by
-- proof
  apply (intervalIntegral.intervalIntegrable_const (c := (1 : ℝ))).mono_fun
  · exact haarMother_stronglyMeasurable.aestronglyMeasurable.restrict
  · apply ae_of_all; intro x; simp only [haarMother]; split_ifs <;> simp

end Chapter3

namespace Chapter3

/--
[haar_ae_first](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Ex_3_9.lean)
-/
@[path]
lemma haar_ae_first
-- imply
  ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc 0 (1/2 : ℝ) → haarMother x = 1 := by
-- proof
  rw [eventually_iff, mem_ae_iff]
  apply measure_mono_null
  show {x : ℝ | x ∈ uIoc 0 (1/2) → haarMother x = 1}ᶜ ⊆ {1/2}
  · intro x hx
    simp only [mem_compl_iff, mem_setOf_eq] at hx; push_neg at hx
    obtain ⟨hxm, hne⟩ := hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/2), mem_Ioc] at hxm
    simp only [mem_singleton_iff]; by_contra h
    exact hne (by unfold haarMother; rw [if_pos ⟨le_of_lt hxm.1, lt_of_le_of_ne hxm.2 h⟩])
  · simp

end Chapter3


-- created on 2026-10-23
