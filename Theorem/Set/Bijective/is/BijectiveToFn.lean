module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3.Part2
public import Theorem.Set.OneToOne.is.InjectiveToFn
public import Theorem.Set.Onto.is.SurjectiveToFn
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


public section

/--
[Function.bijective_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y} :
-- imply
  f.bijective ↔ Function.Bijective f.to_fn :=
-- proof
  by
    rw [Function.bijective, Function.Bijective, OneToOne.is.InjectiveToFn, Onto.is.SurjectiveToFn]


-- created on 2026-10-22
-- updated on 2026-10-26
