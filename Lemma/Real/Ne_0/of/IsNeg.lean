import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.nonzero_of_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real}
-- given
  (hx: x.IsNeg) :
-- imply
  x ≠ 0 :=
-- proof
  Chapter5.Real.nonzero_of_neg hx


-- created on 2026-10-22
