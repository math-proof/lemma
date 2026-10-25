import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Theorem.Analysis.MeasureTheory.Section_1_2_1
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


noncomputable def set_dist {X:Type*} [PseudoMetricSpace X] (A B: Set X) : ℝ :=
  sInf ((fun p: X × X ↦ dist p.1 p.2) '' (A ×ˢ B))

-- ========================================================================
-- Start of Helpers for lemma 1.2.5: Lebesgue_outer_measure.union_of_separated
-- ========================================================================

namespace BoundedInterval

/-- Extract the left and right endpoints of a {name}`BoundedInterval`.
    Returns (a, b) where a is the left endpoint and b is the right endpoint. -/
def endpoints (I : BoundedInterval) : ℝ × ℝ :=
  match I with
  | Ioo a b => (a, b)
  | Icc a b => (a, b)
  | Ioc a b => (a, b)
  | Ico a b => (a, b)

/-- Compute the midpoint of a {name}`BoundedInterval`. -/
noncomputable def midpoint (I : BoundedInterval) : ℝ :=
  let (a, b) := I.endpoints
  (a + b) / 2

/-- Bisect a {name}`BoundedInterval` into left and right halves using closed intervals.
    Left half: \[a, m\], Right half: \[m, b\], where m is the midpoint.
    Using closed intervals ensures coverage (union equals original) while
    maintaining measure-theoretic properties (overlap has measure zero). -/
noncomputable def bisect (I : BoundedInterval) : BoundedInterval × BoundedInterval :=
  let (a, b) := I.endpoints
  let m := I.midpoint
  (Icc a m, Icc m b)

end BoundedInterval
