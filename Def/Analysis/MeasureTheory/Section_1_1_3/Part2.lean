module
public import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
public import Abbrev.Analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open Classical in


public section

/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/
-- The Riemann integral value: the limit of Riemann sums (zero if not integrable).
noncomputable def riemannIntegral (f: ℝ → ℝ) (I: BoundedInterval) : ℝ := if h:RiemannIntegrableOn f I then h.2.2.choose else 0

