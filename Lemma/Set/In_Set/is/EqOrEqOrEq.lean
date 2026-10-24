import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
import Lemma.Set.In_Set.is.Eq
import Lemma.Set.In_Union.is.InOrIn
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.mem_triple](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x a b c:Object} :
-- imply
  x ∈ ({a,b,c}:Chapter3.Set) ↔ (x = a ∨ x = b ∨ x = c) :=
-- proof
  by
    simp [Insert.insert, In_Union.is.InOrIn, In_Set.is.Eq]


-- created on 2026-10-22
-- updated on 2026-10-23
