import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.inv_isCauchy_of_boundedAwayZero](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ}
-- given
  (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
-- imply
  ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy :=
-- proof
  Chapter5.Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy


-- created on 2026-10-22
