import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_6
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.pow_fun_eq_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A B : Chapter3.Set}
  {x y : ↑(A ^ B)} :
-- imply
  x = y ↔ pow_fun_equiv x = pow_fun_equiv y :=
-- proof
  Chapter3.SetTheory.Set.pow_fun_eq_iff x y


-- created on 2026-10-22
