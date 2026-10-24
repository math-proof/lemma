import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3_fn
import Lemma.Nat.Eq_F333a.is.Eq_Add_1
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Nat


/--
[SetTheory.Set.f_3_3_3a_eval'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n: ℕ} :
-- imply
  f_3_3_3a (n:Nat) = (n+1:ℕ) :=
-- proof
  by
    symm
    simp only [Eq_F333a.is.Eq_Add_1, nat_equiv_coe_of_coe]


-- created on 2026-10-22
-- updated on 2026-10-23
