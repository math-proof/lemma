import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.Ioi_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real} :
-- imply
  .Ioi x = { z | z > x } :=
-- proof
  Chapter5.Real.Ioi_def x


-- created on 2026-10-22
