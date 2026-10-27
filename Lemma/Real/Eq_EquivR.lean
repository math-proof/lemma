import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_epilogue.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.equivR_int](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {n: ℤ} :
-- imply
  equivR n = (n: ℝ) :=
-- proof
  Chapter5.Real.equivR_int


-- created on 2026-10-22
