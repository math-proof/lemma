import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.mul_lt_mul_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x y z:Chapter5.Real}
-- given
  (hxy: x < y)
  (hz: z.IsPos) :
-- imply
  x * z < y * z :=
-- proof
  Chapter5.Real.mul_lt_mul_right hxy hz


-- created on 2026-10-22
