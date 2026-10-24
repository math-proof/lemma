import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
import Lemma.Set.EqGetMkFn
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.comp_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y Z: Chapter3.Set}
  {g: Function Y Z}
  {f: Function X Y}
  {x: X} :
-- imply
  (g ○ f) x = g (f x) :=
-- proof
  EqGetMkFn


-- created on 2026-10-22
-- updated on 2026-10-23
