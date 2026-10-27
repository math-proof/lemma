import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_2_2.Part2
import Lemma.Nat.Add.of.IsPos
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.lt_of_le_of_lt](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b c : Chapter2.Nat}
-- given
  (hab: a ≤ b)
  (hbc: b < c) :
-- imply
  a < c :=
-- proof
  by
    rw [lt_iff_add_pos] at *
    choose d hd using hab
    choose e he1 he2 using hbc
    use d + e
    constructor
    · exact Add.of.IsPos he1
    rw [he2, hd, add_assoc]


-- created on 2026-10-22
-- updated on 2026-10-26
