import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.inv_mul_self](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d} [h:NeZero q] :
-- imply
  (q.inv:Formal) * (q:Formal) = 1 :=
-- proof
  UnitsSystem.Scalar.inv_mul_self q


-- created on 2026-10-22
