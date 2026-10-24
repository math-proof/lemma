import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_3
import Lemma.Nat.Mul.eq.AddMul
import Lemma.Nat.Mul1.eq.Add0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.two_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {m: Chapter2.Nat} :
-- imply
  2 * m = 0 + m + m :=
-- proof
  by
    rw [← one_succ, Mul.eq.AddMul, Mul1.eq.Add0]


-- created on 2026-10-22
-- updated on 2026-10-23
