import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_4
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.mem_iUnion](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {I:Chapter3.Set}
  {A: I → Chapter3.Set}
  {x:Object} :
-- imply
  x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α :=
-- proof
  Chapter3.SetTheory.Set.mem_iUnion A x


-- created on 2026-10-22
