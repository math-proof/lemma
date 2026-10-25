import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.ne_of_gt](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b:Chapter2.Nat} :
-- imply
  a > b → a ≠ b :=
-- proof
  by
    intro h
    exact h.2.symm


-- created on 2026-10-22
-- updated on 2026-10-23
