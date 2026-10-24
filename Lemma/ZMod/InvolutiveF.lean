import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_707
open Mainstep


/--
[f_inv](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {a:ZMod N}
-- given
  (ha: a ∉ B) :
-- imply
  Function.Involutive (f ha) :=
-- proof
  Mainstep.f_inv ha


-- created on 2026-10-22
