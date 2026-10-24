import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_4
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.powerset_axiom](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {F:Object} :
-- imply
  F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F :=
-- proof
  Chapter3.SetTheory.Set.powerset_axiom F


-- created on 2026-10-22
