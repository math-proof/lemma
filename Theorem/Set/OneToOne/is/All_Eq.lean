module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3.Part2
open Chapter3 hiding Nat Set
open Chapter3.Function


public section

/--
[Function.one_to_one_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y} :
-- imply
  f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' :=
-- proof
  by
    peel with x hx; tauto


-- created on 2026-10-22
-- updated on 2026-10-26
