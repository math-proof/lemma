module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_3.Part2
public import Theorem.Nat.Mul.lt.Mul.of.IsPos.Lt
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


public section

/--
[Nat.mul_gt_mul_of_pos_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private theorem main
  {a b c: Chapter2.Nat}
-- given
  (h: a > b)
  (hc: c.IsPos) :
-- imply
  a * c > b * c :=
-- proof
  Mul.lt.Mul.of.IsPos.Lt h hc


-- created on 2026-10-22
-- updated on 2026-10-26
