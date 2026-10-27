import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_2_1
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.succ_ne](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  {n:Chapter2.Nat} :
-- imply
  n++ ≠ 0 :=
-- proof
  by
    by_contra h
    injection h


-- created on 2026-10-22
-- updated on 2026-10-26
