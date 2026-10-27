import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_2_3.Part2
import Lemma.Nat.Mul.eq.AddMul
import Lemma.Nat.Mul0.eq.Zero
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.one_mul'](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {m: Chapter2.Nat} :
-- imply
  1 * m = 0 + m :=
-- proof
  by
    rw [← zero_succ, Mul.eq.AddMul, Mul0.eq.Zero]


-- created on 2026-10-22
-- updated on 2026-10-26
