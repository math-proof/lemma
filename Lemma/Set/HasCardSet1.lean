import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.Example_3_6_7a](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {a:Object} :
-- imply
  ({a}:Chapter3.Set).has_card 1 :=
-- proof
  Chapter3.SetTheory.Set.Example_3_6_7a a


-- created on 2026-10-22
