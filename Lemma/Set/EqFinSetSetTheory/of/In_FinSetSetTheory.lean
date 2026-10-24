import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_5
open Chapter3.SetTheory.Set hiding Fin
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set.Fin


/--
[SetTheory.Set.Fin.coe_eq_iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n m:ℕ}
  {i: Chapter3.SetTheory.Set.Fin n}
-- given
  (hi : ↑i ∈ Chapter3.SetTheory.Set.Fin m) :
-- imply
  ((⟨i, hi⟩ : Chapter3.SetTheory.Set.Fin m):ℕ) = (i:ℕ) :=
-- proof
  Chapter3.SetTheory.Set.Fin.coe_eq_iff' i hi


-- created on 2026-10-22
