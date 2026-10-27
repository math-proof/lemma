import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.eq_diff](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {n:Section_4_1.Int} :
-- imply
  ∃ a b, n = a —— b :=
-- proof
  Section_4_1.Int.eq_diff n


-- created on 2026-10-22
