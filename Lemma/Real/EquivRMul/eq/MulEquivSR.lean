import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_epilogue.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.equivR_map_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {x y : Chapter5.Real} :
-- imply
  equivR (x * y) = equivR x * equivR y :=
-- proof
  Chapter5.Real.equivR_map_mul


-- created on 2026-10-22
