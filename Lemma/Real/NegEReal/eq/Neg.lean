import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.neg_of_real](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {x:Real} :
-- imply
  -(x:EReal) = (-x:ℝ) :=
-- proof
  EReal.neg_of_real x


-- created on 2026-10-22
