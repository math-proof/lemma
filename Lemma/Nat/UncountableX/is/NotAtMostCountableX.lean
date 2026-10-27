import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_8_3
open Chapter8
open Chapter8.Uncountable


/--
[Uncountable.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  Uncountable X ↔ ¬ AtMostCountable X :=
-- proof
  Chapter8.Uncountable.iff X


-- created on 2026-10-22
