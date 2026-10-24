import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_5
open Chapter3.SetTheory.Set hiding Fin
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mem_Fin](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ}
  {x:Object} :
-- imply
  x ∈ Chapter3.SetTheory.Set.Fin n ↔ ∃ m, m < n ∧ x = m :=
-- proof
  Chapter3.SetTheory.Set.mem_Fin n x


-- created on 2026-10-22
