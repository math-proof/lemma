import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.triple_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {a b c:Object} :
-- imply
  {a,b,c} = ({a}:Chapter3.Set) ∪ {b,c} :=
-- proof
  by
    rfl


-- created on 2026-10-22
-- updated on 2026-10-23
