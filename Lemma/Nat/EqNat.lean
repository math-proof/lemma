import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.nat_equiv_coe_of_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ} :
-- imply
  ((n:Chapter3.Nat):ℕ) = n :=
-- proof
  Equiv.symm_apply_apply Chapter3.SetTheory.Set.nat_equiv n


-- created on 2026-10-22
-- updated on 2026-10-23
