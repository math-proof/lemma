import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_6_5
open Chapter6
open Chapter6.Sequence


/--
[Sequence.pow_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_5.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {k: ℕ}
  {n: ℤ}
-- given
  (hn : n ≥ a.m) :
-- imply
  (a ^ k) n = a n ^ k :=
-- proof
  Chapter6.Sequence.pow_eval hn


-- created on 2026-10-22
