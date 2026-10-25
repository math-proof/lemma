import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set hiding Fin
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set.Fin


/--
[SetTheory.Set.Fin.coe_eq_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ}
  {i: Chapter3.SetTheory.Set.Fin n}
  {j:ℕ} :
-- imply
  (i:Object) = (j:Object) ↔ i = j :=
-- proof
  Chapter3.SetTheory.Set.Fin.coe_eq_iff i


-- created on 2026-10-22
