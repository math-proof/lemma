import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_4
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.example_3_4_9](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_4.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {F:Object} :
-- imply
  F ∈ ({0,1}:Chapter3.Set) ^ ({4,7}:Chapter3.Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d  :=
-- proof
  Chapter3.SetTheory.Set.example_3_4_9 F


-- created on 2026-10-22
