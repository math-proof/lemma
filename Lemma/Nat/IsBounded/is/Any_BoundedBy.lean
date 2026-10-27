import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5


/--
[isBounded_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {a:Sequence} :
-- imply
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M :=
-- proof
  Chapter5.Sequence.isBounded_def a


-- created on 2026-10-20
