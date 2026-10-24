import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.All.of.All_Nat_induction
import Lemma.Nat.Eq_Add0
import Lemma.Nat.AddEqAdd
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_pos_left](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b : Chapter2.Nat}
-- given
  (ha: a.IsPos) :
-- imply
  (a + b).IsPos :=
-- proof
  by
    revert b
    apply All.of.All_Nat_induction
    · rwa [Eq_Add0]
    intro b hab
    rw [AddEqAdd]
    have : (a + b)++ ≠ 0 := succ_ne _
    exact this


-- created on 2026-10-22
-- updated on 2026-10-23
