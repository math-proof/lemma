import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_2_3.Part2
import Lemma.Nat.Eq1Mul
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.mul_one](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {m: Chapter2.Nat} :
-- imply
  m * 1 = m :=
-- proof
  by
    rw [mul_comm, Eq1Mul]


-- created on 2026-10-22
-- updated on 2026-10-26
