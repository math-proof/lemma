import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.LUB_unique](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
  {M M': Chapter5.Real}
-- given
  (h0: IsLUB E M)
  (h1: IsLUB E M') :
-- imply
  M = M' :=
-- proof
  Chapter5.Real.LUB_unique h0 h1


-- created on 2026-10-22
