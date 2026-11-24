module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3.Part2
public import Lemma.Set.EqGetMkFn
public import Lemma.Set.Eq.is.All_Eq
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


public section

/--
[SetTheory.Set.f_3_3_10_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  :
-- imply
  f_3_3_10a = f_3_3_10b :=
-- proof
  by
    simp_rw [Eq.is.All_Eq, EqGetMkFn]
    intros; simp; ring


-- created on 2026-10-22
-- updated on 2026-10-26
