import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set hiding Fin
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mem_Fin'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ}
  {x:Chapter3.SetTheory.Set.Fin n} :
-- imply
  ∃ m, ∃ h : m < n, x = Fin_mk n m h :=
-- proof
  Chapter3.SetTheory.Set.mem_Fin' x


-- created on 2026-10-22
