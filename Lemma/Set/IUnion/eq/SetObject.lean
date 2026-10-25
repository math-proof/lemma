import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_4.Part8
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.iUnion_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {I: Chapter3.Set}
  {A: I → Chapter3.Set} :
-- imply
  (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) :=
-- proof
  Chapter3.SetTheory.Set.iUnion_eq I A


-- created on 2026-10-22
