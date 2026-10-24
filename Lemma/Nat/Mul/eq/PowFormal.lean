import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_pow](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d}
  {n:ℕ} :
-- imply
  ((q ** n):Formal) = (q:Formal) ^ n :=
-- proof
  UnitsSystem.Scalar.toFormal_pow q n


-- created on 2026-10-22
