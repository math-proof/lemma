import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.Constant


/--
[Constant.const_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {X Y:Type} [hX: Nonempty X] [Nonempty Y]
  {f:X → Y}
  {c:Y}
-- given
  (h: ∀ x, f x = c) :
-- imply
  constant_value f = c :=
-- proof
  Chapter11.Constant.const_eq h


-- created on 2026-10-22
