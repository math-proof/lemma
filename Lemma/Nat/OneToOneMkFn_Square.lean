import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
import Lemma.Set.OneToOne.is.All_Eq
import Lemma.Set.EqGetMkFn
import Lemma.Set.EqIffP
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.f_3_3_18_one_to_one](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  :
-- imply
  (Function.mk_fn (fun (n:Chapter3.Nat) ↦ ((n^2:ℕ):Chapter3.Nat))).one_to_one :=
-- proof
  by
    rw [OneToOne.is.All_Eq]
    intro _ _ h
    simpa [EqIffP, EqGetMkFn] using h


-- created on 2026-10-22
-- updated on 2026-10-23
