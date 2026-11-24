module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Abbrev.Analysis.Section_3_3.Part2
public import Theorem.Set.Eq
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


public section

/--
[Function.comp_eq_comp](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {X Y Z: Chapter3.Set}
  {g: Function Y Z}
  {f: Function X Y} :
-- imply
  (g ○ f).to_fn = g.to_fn ∘ f.to_fn :=
-- proof
  by
    ext; simp only [Set.Eq, Function.comp_apply]


-- created on 2026-10-22
-- updated on 2026-10-26
