import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_4_3.Part2
open Section_4_3 hiding abs dist


/--
[dist_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x y: ℚ} :
-- imply
  Section_4_3.dist x y = |x-y| :=
-- proof
  Section_4_3.dist_eq x y


-- created on 2026-10-22
