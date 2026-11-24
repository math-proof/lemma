module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3.Part2
public import Theorem.Set.EqIffP

public section

open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.eval_of](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: X → Y}
  {x:X} :
-- imply
  (Function.mk_fn f) x = f x :=
-- proof
  by
    symm; rw [EqIffP]


-- created on 2026-10-22
-- updated on 2026-10-26
