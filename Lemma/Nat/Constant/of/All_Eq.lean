import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.Constant


/--
[Constant.of_const](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {X Y:Type}
  {f:X → Y}
  {c:Y}
-- given
  (h: ∀ x, f x = c) :
-- imply
  Constant f :=
-- proof
  Chapter11.Constant.of_const h


-- created on 2026-10-22
