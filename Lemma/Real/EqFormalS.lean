import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Formal


/--
[Formal.coe_int](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {n:ℤ} :
-- imply
  ((n:ℝ):Formal) = (n:Formal) :=
-- proof
  UnitsSystem.Formal.coe_int n


-- created on 2026-10-22
