import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
import Lemma.Nat.All.of.All_Nat_induction
import Lemma.Nat.Eq0Add
import Lemma.Nat.Eq_Add0
import Lemma.Nat.Eq_Add
import Lemma.Nat.AddEqAdd
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_comm](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {n m:Chapter2.Nat} :
-- imply
  n + m = m + n :=
-- proof
  by
    revert n
    apply All.of.All_Nat_induction
    · rw [Eq0Add, Eq_Add0]
    intro n ih
    rw [Eq_Add]
    rw [AddEqAdd, ih]


-- created on 2026-10-22
-- updated on 2026-10-23
