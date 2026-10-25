import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.trichotomous](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {x:Section_4_1.Int} :
-- imply
  x = 0 ∨ x.IsPos ∨ x.IsNeg :=
-- proof
  Section_4_1.Int.trichotomous x


-- created on 2026-10-22
