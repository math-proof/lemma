import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_2_2.Part2
import Lemma.Nat.All.of.All_Nat_induction
import Lemma.Nat.Eq0Add
import Lemma.Nat.Eq_Add
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_left_cancel](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b c:Chapter2.Nat}
-- given
  (habc: a + b = a + c) :
-- imply
  b = c :=
-- proof
  by
    revert a
    apply All.of.All_Nat_induction
    ·
      intro hbc
      rwa [Eq0Add, Eq0Add] at hbc
    intro a ih hbc
    rw [Eq_Add, Eq_Add] at hbc
    replace hbc := succ_cancel hbc
    exact ih hbc


-- created on 2026-10-22
-- updated on 2026-10-26
