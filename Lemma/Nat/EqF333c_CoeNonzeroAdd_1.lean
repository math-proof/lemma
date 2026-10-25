import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_3_fn
import Lemma.Set.Eq_F333c.is.EqAdd_1
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.f_3_3_3c_eval'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n: ℕ} :
-- imply
  f_3_3_3c (coe_nonzero (n+1) (by positivity)) = n :=
-- proof
  by
    symm; simp [Eq_F333c.is.EqAdd_1]


-- created on 2026-10-22
-- updated on 2026-10-23
