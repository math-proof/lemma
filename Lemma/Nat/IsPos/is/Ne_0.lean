import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_2_2.Part2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.isPos_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {n:Chapter2.Nat} :
-- imply
  n.IsPos ↔ n ≠ 0 :=
-- proof
  by rfl


-- created on 2026-10-22
-- updated on 2026-10-26
