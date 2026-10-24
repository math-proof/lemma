import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_epilogue
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.equivR_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {x: Chapter5.Real} :
-- imply
  ∃(a : ℕ → ℚ) (ha: Sequence.IsCauchy a),
    x = LIM a ∧ x.equivR = Real.mk ha.CauSeq :=
-- proof
  Chapter5.Real.equivR_eq x


-- created on 2026-10-22
