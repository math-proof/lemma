import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.inv_of_gt](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x y:Chapter5.Real}
-- given
  (hx: x.IsPos)
  (hy: y.IsPos)
  (hxy: x > y) :
-- imply
  x⁻¹ < y⁻¹ :=
-- proof
  Chapter5.Real.inv_of_gt hx hy hxy


-- created on 2026-10-22
