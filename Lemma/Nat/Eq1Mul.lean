import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_2_3.Part2
import Lemma.Nat.Mul1.eq.Add0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.one_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {m: Chapter2.Nat} :
-- imply
  1 * m = m :=
-- proof
  by
    rw [Mul1.eq.Add0, zero_add]


-- created on 2026-10-22
-- updated on 2026-10-26
