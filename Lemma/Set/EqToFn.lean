import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
open Chapter3 hiding Nat Set
open Chapter3.Function


/--
[Function.to_fn_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y}
  {x:X} :
-- imply
  f.to_fn x = f x :=
-- proof
  rfl


-- created on 2026-10-22
-- updated on 2026-10-23
