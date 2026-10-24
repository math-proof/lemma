import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
import Lemma.Set.EqGetMkFn
import Lemma.Set.Eq.is.All_Eq
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.f_circ_g_3_3_14](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  :
-- imply
  f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):Nat)) :=
-- proof
  by
    simp [Eq.is.All_Eq, EqGetMkFn]
    intros; ring


-- created on 2026-10-22
-- updated on 2026-10-23
