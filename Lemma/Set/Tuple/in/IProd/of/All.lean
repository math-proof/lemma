import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.tuple_mem_iProd](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {I: Chapter3.Set}
  {X: I → Chapter3.Set}
-- given
  (x: ∀ i, X i) :
-- imply
  tuple x ∈ iProd X :=
-- proof
  Chapter3.SetTheory.Set.tuple_mem_iProd x


-- created on 2026-10-22
