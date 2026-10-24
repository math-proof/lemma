import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
open Chapter3 hiding Nat Set
open Chapter3.Function


/--
[Function.one_to_one_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y} :
-- imply
  f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' :=
-- proof
  by
    peel with x hx; tauto


-- created on 2026-10-22
-- updated on 2026-10-23
