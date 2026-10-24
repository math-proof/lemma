import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_5
open Chapter3.SetTheory.Set hiding Fin
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set.Fin


/--
[SetTheory.Set.Fin.coe_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ}
  {i j: Chapter3.SetTheory.Set.Fin n} :
-- imply
  i = j ↔ (i:ℕ) = (j:ℕ) :=
-- proof
  Chapter3.SetTheory.Set.Fin.coe_inj


-- created on 2026-10-22
