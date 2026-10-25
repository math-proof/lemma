import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_3.Part2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.mul_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {a b c: Chapter2.Nat} :
-- imply
  a * (b + c) = a * b + a * c :=
-- proof
  by
    revert c
    apply induction
    ·
      rw [add_zero]
      rw [mul_zero, add_zero]
    intro c habc
    rw [add_succ, mul_succ]
    rw [mul_succ, ← add_assoc, ← habc]


-- created on 2026-10-22
-- updated on 2026-10-23
