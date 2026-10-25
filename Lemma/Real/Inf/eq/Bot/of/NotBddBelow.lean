import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.ExtendedReal


/--
[ExtendedReal.inf_of_unbounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
-- given
  (hb: ¬ BddBelow E) :
-- imply
  inf E = ⊥ :=
-- proof
  Chapter5.ExtendedReal.inf_of_unbounded hb


-- created on 2026-10-22
