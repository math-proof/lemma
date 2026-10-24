import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[not_isA1_and_isB1](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {v : V} :
-- imply
  ¬ (isA1 v ∧ isB1 v) :=
-- proof
  PikhurkoN5.not_isA1_and_isB1 v


-- created on 2026-10-22
