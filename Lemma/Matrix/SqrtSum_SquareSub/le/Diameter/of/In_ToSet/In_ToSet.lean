import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Box


/--
[dist_le_diameter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {x y: EuclideanSpace' d}
-- given
  (hx: x ∈ B.toSet)
  (hy: y ∈ B.toSet) :
-- imply
  √(∑ i, (x i - y i)^2) ≤ B.diameter :=
-- proof
  Box.dist_le_diameter B hx hy


-- created on 2026-10-22
