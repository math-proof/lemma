import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
import Theorem.Analysis.MeasureTheory.Section_1_2_2.Part2
  IsOpen.measurable isOpen_empty

  intro ε hε
  use ∅
  constructor
  · exact isOpen_empty
  constructor
  · exact Set.empty_subset ∅
  · have h_empty : ∅ \ ∅ = (∅ : Set (EuclideanSpace' d)) := Set.diff_self
    rw [h_empty]
    rw [Lebesgue_outer_measure.of_empty d]
    exact le_of_lt hε

open BoundedInterval


abbrev CantorInterval (n:ℕ) : Set ℝ := ⋃ a : Fin n → ({0, 2}:Set ℕ), (Icc (∑ i, (a i)/(3:ℝ)^(i.val+1)) (∑ i, a i/(3:ℝ)^(i.val+1) + 1/(3:ℝ)^n)).toSet

abbrev CantorSet : Set ℝ := ⋂ n : ℕ, CantorInterval n

