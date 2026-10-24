import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_2
open EReal


/--
[EReal.inf_eq_neg_sup](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {E: Set EReal} :
-- imply
  sInf E = - sSup (-E) :=
-- proof
  EReal.inf_eq_neg_sup E


-- created on 2026-10-22
