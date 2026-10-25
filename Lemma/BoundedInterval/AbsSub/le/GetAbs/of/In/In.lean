import Mathlib
import sympy.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.dist_le_length](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I:BoundedInterval}
  {x y:ℝ}
-- given
  (hx: x ∈ I)
  (hy: y ∈ I) :
-- imply
  |x - y| ≤ |I|ₗ :=
-- proof
  Chapter11.BoundedInterval.dist_le_length hx hy


-- created on 2026-10-22
