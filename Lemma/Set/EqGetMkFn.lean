import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
import Lemma.Set.EqIffP
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.eval_of](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
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
-- updated on 2026-10-23
