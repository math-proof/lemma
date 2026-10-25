import Mathlib
import sympy.Basic
import Theorem.Analysis.Appendix_A_2


/--
[contrapositive](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_2.lean)
-/
@[path]
private lemma main
  {X Y: Prop}
-- given
  (hXY: X → Y) :
-- imply
  ¬ Y → ¬ X :=
-- proof
  contrapositive hXY


-- created on 2026-10-20
