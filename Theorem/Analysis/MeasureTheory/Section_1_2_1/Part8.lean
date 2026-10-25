import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part7
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Remark_1_2_8

lemma q_mem (n : ℕ) : q n ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun r:ℚ ↦ (r:ℝ)) :=
  (q_enum n).property

lemma q_in_unit_interval (n : ℕ) : q n ∈ Set.Icc (0:ℝ) 1 := (q_mem n).1

lemma q_surj : ∀ x ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun r:ℚ ↦ (r:ℝ)), ∃ n, q n = x := by
  intro x hx
  obtain ⟨n, hn⟩ := q_enum_surj ⟨x, hx⟩
  use n
  unfold q
  rw [hn]

end Remark_1_2_8
