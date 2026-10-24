import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.mul_inv_self](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d} [h:NeZero q] :
-- imply
  (q:Formal) * (q.inv:Formal) = 1 :=
-- proof
  UnitsSystem.Scalar.mul_inv_self q


-- created on 2026-10-22
