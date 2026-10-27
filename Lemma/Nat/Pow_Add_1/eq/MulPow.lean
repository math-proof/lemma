import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_6_5
open Chapter6
open Chapter6.Sequence


/--
[Sequence.pow_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_5.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {k:ℕ} :
-- imply
  a^(k+1) = a^k * a :=
-- proof
  Chapter6.Sequence.pow_succ a k


-- created on 2026-10-22
