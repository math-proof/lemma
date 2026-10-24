import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mem_singleton](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x a:Object} :
-- imply
  x ∈ ({a}:Chapter3.Set) ↔ x = a :=
-- proof
  singleton_axiom x a


-- created on 2026-10-22
-- updated on 2026-10-23
