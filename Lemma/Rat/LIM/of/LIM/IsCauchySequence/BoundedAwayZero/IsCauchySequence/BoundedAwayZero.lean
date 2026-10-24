import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_3
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.inv_of_equiv](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a b:ℕ → ℚ}
-- given
  (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy)
  (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy)
  (hlim: LIM a = LIM b) :
-- imply
  LIM a⁻¹ = LIM b⁻¹ :=
-- proof
  Chapter5.Real.inv_of_equiv ha ha_cauchy hb hb_cauchy hlim


-- created on 2026-10-22
