module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3.Part2
open Chapter3 hiding Nat Set
open Chapter3.Function


public section

/--
[Function.onto_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y} :
-- imply
  f.onto ↔ Function.Surjective f.to_fn :=
-- proof
  by rfl


-- created on 2026-10-22
-- updated on 2026-10-26
