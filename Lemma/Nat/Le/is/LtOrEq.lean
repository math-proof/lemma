import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
import Lemma.Nat.Le.is.Any_Eq_Add
import Lemma.Nat.Lt.is.Any_Eq_AddAndNe
import Lemma.Nat.Eq_Add0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.le_iff_lt_or_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {n m:Chapter2.Nat} :
-- imply
  n ≤ m ↔ n < m ∨ n = m :=
-- proof
  by
    rw [Le.is.Any_Eq_Add, Lt.is.Any_Eq_AddAndNe]
    if h : n = m then
      simp [h]
      use 0
      rw [Eq_Add0]
    else
      simp [h]


-- created on 2026-10-22
-- updated on 2026-10-23
