module
public import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
public import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part3
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.1.3: Connections with the Riemann integral

A companion to Section 1.1.3 of the book "An introduction to Measure Theory".

-/
/-- For any x in \[a,b\], find the subinterval index containing x -/
noncomputable def findSubintervalIndex (lo hi : ℝ) (n : ℕ) (hn : n > 0) (x : ℝ) (_hx : lo ≤ x ∧ x ≤ hi) : Fin n :=
  let k := min (Nat.floor ((x - lo) / ((hi - lo) / n))) (n - 1)
  ⟨k, by omega⟩

