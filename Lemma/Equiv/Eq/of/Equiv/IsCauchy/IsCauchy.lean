import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_epilogue.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.mk_eq_mk](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {a b: ℕ → ℚ}
-- given
  (ha : Sequence.IsCauchy a)
  (hb : Sequence.IsCauchy b)
  (hab: Sequence.Equiv a b) :
-- imply
  Real.mk ha.CauSeq = Real.mk hb.CauSeq :=
-- proof
  Chapter5.Real.mk_eq_mk ha hb hab


-- created on 2026-10-22
