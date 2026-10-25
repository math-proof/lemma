import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_3_fn
import Lemma.Nat.F333aNat.eq.Add_1
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Nat


/--
[SetTheory.Set.f_3_3_3a_eval''](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  :
-- imply
  f_3_3_3a 4 = 5 :=
-- proof
  F333aNat.eq.Add_1 (n := 4)


-- created on 2026-10-22
-- updated on 2026-10-23
