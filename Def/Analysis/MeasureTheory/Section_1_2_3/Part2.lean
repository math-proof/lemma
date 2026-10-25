import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
import Theorem.Analysis.MeasureTheory.Section_1_2_3
open scoped Pointwise

/-!
# Introduction to Measure Theory, Section 1.2.3: Non-measurable sets

A companion to (the introduction to) Section 1.2.3 of the book "An introduction to Measure Theory".

-/


/-- The Vitali set: choose one representative from each coset that lies in \[0,1\] -/
noncomputable def VitaliSet : Set ℝ :=
  Set.range (fun c : RealModRat => (coset_intersects_unit_interval c).choose)

