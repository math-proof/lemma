import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.Le.of.Lt_Nat_le_of_lt
import Lemma.Nat.Ne_Nat_ne_of_lt
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.not_lt_of_gt](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b:Chapter2.Nat} :
-- imply
  a < b ∧ a > b → False :=
-- proof
  by
    intro h
    have := (ge_antisymm (Le.of.Lt_Nat_le_of_lt h.1) (Le.of.Lt_Nat_le_of_lt h.2)).symm
    have := Ne_Nat_ne_of_lt h.1
    contradiction


-- created on 2026-10-22
-- updated on 2026-10-23
