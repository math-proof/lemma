module
public import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
public import Theorem.Analysis.Misc.RealERealENNReal
public import Theorem.Analysis.Misc.Combinatorics
public import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part6
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/
namespace Remark_1_2_8

/-- An enumeration function of rationals in \[0,1\] -/
noncomputable def q_enum : ℕ → { x : ℝ // x ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun q:ℚ ↦ (q:ℝ)) } :=
  (rationals_unit_interval_countable.exists_surjective rationals_unit_interval_nonempty).choose

end Remark_1_2_8
