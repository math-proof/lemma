module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_3.Part2
public import Theorem.Nat.MulAddEqAddMulS
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


public section

/--
[Nat.add_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private theorem main
  {a b c: Chapter2.Nat} :
-- imply
  (a + b)*c = a*c + b*c :=
-- proof
  by
    simp only [mul_comm, MulAddEqAddMulS]


-- created on 2026-10-22
-- updated on 2026-10-26
