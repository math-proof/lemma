import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_6
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.finite_iff_set_finite](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X:Chapter3.Set} :
-- imply
  X.finite ↔ (X :_root_.Set Object).Finite :=
-- proof
  Chapter3.SetTheory.Set.finite_iff_set_finite


-- created on 2026-10-22
