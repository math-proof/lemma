module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3_inv
public import Lemma.Set.EqIffP
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


public section

/--
[Function.inverse_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y}
  {y: Y}
  {x: X}
-- given
  (h: f.bijective) :
-- imply
  x = (f.inverse h) y ↔ f x = y :=
-- proof
  EqIffP


-- created on 2026-10-22
-- updated on 2026-10-26
