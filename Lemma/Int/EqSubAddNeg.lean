import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.sub_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b:Section_4_1.Int} :
-- imply
  a - b = a + (-b) :=
-- proof
  Section_4_1.Int.sub_eq a b


-- created on 2026-10-22
