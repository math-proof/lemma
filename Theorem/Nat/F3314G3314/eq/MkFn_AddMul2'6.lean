module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3.Part2
public import Theorem.Set.EqGetMkFn
public import Theorem.Set.Eq.is.All_Eq

public section

open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


/--
[SetTheory.Set.f_circ_g_3_3_14](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  :
-- imply
  f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):Nat)) :=
-- proof
  by
    simp [Eq.is.All_Eq, EqGetMkFn]
    intros; ring


-- created on 2026-10-22
-- updated on 2026-10-26
