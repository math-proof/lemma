import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.All.of.All_Nat_induction
import Lemma.Nat.Eq0Add
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {n:Chapter2.Nat} :
-- imply
  n + 0 = n :=
-- proof
  by
    revert n
    apply All.of.All_Nat_induction
    · exact Eq0Add
    intro n ih
    calc
      _ = (n + 0)++ := by rfl
      _ = n++ := by rw [ih]


-- created on 2026-10-22
-- updated on 2026-10-23
