import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3_fn
import Lemma.Set.EqIffP
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.f_3_3_5_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x: Nat} :
-- imply
  f_3_3_5 x = 7 :=
-- proof
  by
    symm; rw [EqIffP]


-- created on 2026-10-22
-- updated on 2026-10-23
