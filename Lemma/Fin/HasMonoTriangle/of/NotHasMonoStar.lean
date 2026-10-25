import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[red_triangle_of_no_blue_star](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
-- given
  (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
-- imply
  hasMonoTriangle G color 1 :=
-- proof
  PikhurkoN5.red_triangle_of_no_blue_star color hNoBlueStar


-- created on 2026-10-22
