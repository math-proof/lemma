import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[map_finite_series](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  [Fintype X] [Fintype Y]
  {f: X → ℝ}
  {g:Y → X}
-- given
  (hg: Function.Bijective g) :
-- imply
  ∑ x, f x = ∑ y, f (g y) :=
-- proof
  Finset.map_finite_series f hg


-- created on 2026-10-20
