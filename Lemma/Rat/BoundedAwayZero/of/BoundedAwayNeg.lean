import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_4
open Chapter5 hiding Real
open Chapter5.BoundedAwayZero


/--
[BoundedAwayZero.boundedAwayNeg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ}
-- given
  (ha: BoundedAwayNeg a) :
-- imply
  BoundedAwayZero a :=
-- proof
  Chapter5.BoundedAwayZero.boundedAwayNeg ha


-- created on 2026-10-22
