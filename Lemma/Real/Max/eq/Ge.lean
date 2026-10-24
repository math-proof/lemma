import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.max_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x y:Chapter5.Real} :
-- imply
  max x y = if x ≥ y then x else y :=
-- proof
  Chapter5.Real.max_eq x y


-- created on 2026-10-22
