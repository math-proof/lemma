import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Formal


/--
[Formal.smul_eq_mul''](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {c:ℤ}
  {x:Formal} :
-- imply
  c • x = (c:Formal) * x :=
-- proof
  UnitsSystem.Formal.smul_eq_mul'' c x


-- created on 2026-10-22
