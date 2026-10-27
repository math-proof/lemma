import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.min_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a b: Sequence}
  {n:ℤ} :
-- imply
  (a ⊓ b) n = (a n) ⊓ (b n) :=
-- proof
  Chapter6.Sequence.min_eval n


-- created on 2026-10-22
