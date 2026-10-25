import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.ExtendedReal


/--
[ExtendedReal.finite_eq_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {X: ExtendedReal}
-- given
  (hX: X.IsFinite) :
-- imply
  X = ((X:Chapter5.Real):ExtendedReal) :=
-- proof
  Chapter5.ExtendedReal.finite_eq_coe hX


-- created on 2026-10-22
