import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2


/--
[choose_spec](https://github.com/teorth/analysis/blob/main/Analysis/Tools/ExistsUnique.lean)
-/
@[path]
private lemma main
  [hs: Subsingleton α] [Nonempty α]
  {x:α} :
-- imply
  x = hs.choose :=
-- proof
  Subsingleton.choose_spec x


-- created on 2026-10-20
