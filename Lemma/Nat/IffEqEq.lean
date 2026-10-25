import Mathlib
import sympy.Basic
import Instance.Analysis.Section_3_1.Part5
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.nat_equiv_symm_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n m:Chapter3.Nat} :
-- imply
  (n:ℕ) = (m:ℕ) ↔ n = m :=
-- proof
  Equiv.apply_eq_iff_eq Chapter3.SetTheory.Set.nat_equiv.symm


-- created on 2026-10-22
-- updated on 2026-10-23
