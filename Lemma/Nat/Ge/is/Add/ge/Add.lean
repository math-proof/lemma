import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.EqAddAdd
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_ge_add_left](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b c:Chapter2.Nat} :
-- imply
  a ≥ b ↔ c + a ≥ c + b :=
-- proof
  by
    simp only [EqAddAdd]
    exact add_ge_add_right a b c


-- created on 2026-10-22
-- updated on 2026-10-23
