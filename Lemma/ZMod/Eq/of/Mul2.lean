import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_707.Part5
open Mainstep


/--
[mul_two_inj](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {x y: ZMod N}
-- given
  (h: 2 * x = 2 * y) :
-- imply
  x = y :=
-- proof
  Mainstep.mul_two_inj h


-- created on 2026-10-22
