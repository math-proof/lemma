import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_3
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.inv_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ}
-- given
  (h: BoundedAwayZero a)
  (hc: (a:Sequence).IsCauchy) :
-- imply
  (LIM a)⁻¹ = LIM a⁻¹ :=
-- proof
  Chapter5.Real.inv_def h hc


-- created on 2026-10-22
