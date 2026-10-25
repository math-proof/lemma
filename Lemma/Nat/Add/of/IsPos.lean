import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
import Lemma.Nat.EqAddAdd
import Lemma.Nat.IsPosAdd.of.IsPos
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_pos_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b : Chapter2.Nat}
-- given
  (ha: a.IsPos) :
-- imply
  (b + a).IsPos :=
-- proof
  by
    rw [EqAddAdd]
    exact IsPosAdd.of.IsPos ha


-- created on 2026-10-22
-- updated on 2026-10-23
