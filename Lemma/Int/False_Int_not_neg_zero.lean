import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_1
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.not_neg_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {x:Section_4_1.Int} :
-- imply
  x = 0 ∧ x.IsNeg → False :=
-- proof
  Section_4_1.Int.not_neg_zero x


-- created on 2026-10-22
