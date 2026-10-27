import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_3_fn
import Lemma.Nat.EqF333c_CoeNonzeroAdd_1
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Nat


/--
[SetTheory.Set.f_3_3_3c_eval''](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  :
-- imply
  f_3_3_3c (coe_nonzero 4 (by positivity)) = 3 :=
-- proof
  by
    convert EqF333c_CoeNonzeroAdd_1 (n := 3)


-- created on 2026-10-22
-- updated on 2026-10-26
