import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.Eq_Add
import Lemma.Nat.Eq0Add
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.one_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {m:Chapter2.Nat} :
-- imply
  1 + m = m++ :=
-- proof
  by
    rw [show 1 = 0++ from rfl, Eq_Add, Eq0Add]


-- created on 2026-10-22
-- updated on 2026-10-23
