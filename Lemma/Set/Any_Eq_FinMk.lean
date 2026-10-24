import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_5
open Chapter3.SetTheory.Set hiding Fin
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set.Fin


/--
[SetTheory.Set.Fin.toNat_spec](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ}
  {i: Chapter3.SetTheory.Set.Fin n} :
-- imply
  ∃ h : i < n, i = Fin_mk n i h :=
-- proof
  Chapter3.SetTheory.Set.Fin.toNat_spec i


-- created on 2026-10-22
