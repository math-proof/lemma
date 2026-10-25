import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
import Lemma.Nat.Eq_Add
import Lemma.Nat.EqAdd1
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.two_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {m:Chapter2.Nat} :
-- imply
  2 + m = (m++)++ :=
-- proof
  by
    rw [show 2 = 1++ from rfl, Eq_Add, EqAdd1]


-- created on 2026-10-22
-- updated on 2026-10-23
