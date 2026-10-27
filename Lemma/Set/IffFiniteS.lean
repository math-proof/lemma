import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.finite_iff_finite](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set} :
-- imply
  X.finite ↔ Empty.Finite X :=
-- proof
  Chapter3.SetTheory.Set.finite_iff_finite


-- created on 2026-10-22
