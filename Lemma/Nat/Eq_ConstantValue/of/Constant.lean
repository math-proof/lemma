import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.Constant


/--
[Constant.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {X Y:Type} [Nonempty Y]
  {f: X → Y}
  {x:X}
-- given
  (h: Constant f) :
-- imply
  f x = constant_value f :=
-- proof
  Chapter11.Constant.eq h x


-- created on 2026-10-22
