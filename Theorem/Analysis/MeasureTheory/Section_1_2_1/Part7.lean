module
public import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
public import Theorem.Analysis.Misc.RealERealENNReal
public import Theorem.Analysis.Misc.Combinatorics
public import Def.Analysis.MeasureTheory.Section_1_2_1.Part6
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/
namespace Remark_1_2_8

lemma q_enum_surj : Function.Surjective q_enum :=
  (rationals_unit_interval_countable.exists_surjective rationals_unit_interval_nonempty).choose_spec

end Remark_1_2_8
