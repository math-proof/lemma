import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_1
import Lemma.Nat.Eq.of.Eq_Nat_succ_cancel
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.succ_ne_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  {n m:Chapter2.Nat} :
-- imply
  n ≠ m → n++ ≠ m++ :=
-- proof
  by
    intro h
    contrapose! h
    exact Eq.of.Eq_Nat_succ_cancel h


-- created on 2026-10-22
-- updated on 2026-10-23
