import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_9_3.Part2
open Chapter9
open Chapter9.Real


/--
[Real.sign_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_3.lean)
-/
@[path]
private lemma main
  {x:ℝ} :
-- imply
  Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 :=
-- proof
  Chapter9.Real.sign_def x


-- created on 2026-10-22
