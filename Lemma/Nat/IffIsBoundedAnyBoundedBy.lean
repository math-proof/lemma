import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.isBounded_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence} :
-- imply
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M :=
-- proof
  Chapter6.Sequence.isBounded_def a


-- created on 2026-10-22
