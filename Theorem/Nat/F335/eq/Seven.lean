module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3_fn
public import Theorem.Set.EqIffP
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Set


public section

/--
[SetTheory.Set.f_3_3_5_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {x: Nat} :
-- imply
  f_3_3_5 x = 7 :=
-- proof
  by
    symm; rw [EqIffP]


-- created on 2026-10-22
-- updated on 2026-10-26
