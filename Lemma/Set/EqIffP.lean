import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_3.Part2
import Lemma.Set.EqToFn
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y}
  {x: X}
  {y: Y} :
-- imply
  y = f x ↔ f.P x y :=
-- proof
  by
    rw [← EqToFn]
    exact ((f.unique x).choose_iff y).symm


-- created on 2026-10-22
-- updated on 2026-10-26
