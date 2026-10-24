import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mem_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set}
  {x:Object} :
-- imply
  x ∈ (X : _root_.Set Object) ↔ x ∈ X :=
-- proof
  by
    simp


-- created on 2026-10-22
-- updated on 2026-10-23
