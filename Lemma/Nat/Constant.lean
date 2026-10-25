import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.Constant


/--
[Constant.of_subsingleton](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {X Y:Type} [hs: Subsingleton X] [hY: Nonempty Y]
  {f:X → Y} :
-- imply
  Constant f :=
-- proof
  Chapter11.Constant.of_subsingleton


-- created on 2026-10-22
