import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_3
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.nonzero_of_boundedAwayZero](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ}
  {n: ℕ}
-- given
  (ha: BoundedAwayZero a) :
-- imply
  a n ≠ 0 :=
-- proof
  Chapter5.Real.nonzero_of_boundedAwayZero ha n


-- created on 2026-10-22
