import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_3.Part2
import Lemma.Set.Eq
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.comp_eq_comp](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
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
-- updated on 2026-10-23
