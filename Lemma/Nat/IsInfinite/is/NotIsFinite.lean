import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.infinite_iff_not_finite](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {x:EReal} :
-- imply
  x.IsInfinite ↔ ¬ x.IsFinite :=
-- proof
  EReal.infinite_iff_not_finite x


-- created on 2026-10-22
