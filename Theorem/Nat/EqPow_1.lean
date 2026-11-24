module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_3.Part2
public import Theorem.Nat.PowNat.eq.MulPow
public import Theorem.Nat.Pow_0.eq.One
public import Theorem.Nat.Eq1Mul
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


public section

/--
[Nat.pow_one](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private theorem main
  {m: Chapter2.Nat} :
-- imply
  m ^ (1:Chapter2.Nat) = m :=
-- proof
  by
    rw [← zero_succ, PowNat.eq.MulPow, Pow_0.eq.One, Eq1Mul]


-- created on 2026-10-22
-- updated on 2026-10-26
