import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.abs_of_pos](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real}
-- given
  (hx: x.IsPos) :
-- imply
  Chapter5.Real.abs x = x :=
-- proof
  Chapter5.Real.abs_of_pos x hx


-- created on 2026-10-22
