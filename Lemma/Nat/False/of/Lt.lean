import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.False_Nat_not_lt_of_gt
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.not_lt_self](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a: Chapter2.Nat}
-- given
  (h : a < a) :
-- imply
  False :=
-- proof
  by
    apply False_Nat_not_lt_of_gt (a := a) (b := a)
    simp [h]


-- created on 2026-10-22
-- updated on 2026-10-23
