import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.StandardUnit


/--
[StandardUnit.inv](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions} :
-- imply
  (StandardUnit d).inv = StandardUnit (-d) :=
-- proof
  UnitsSystem.StandardUnit.inv d


-- created on 2026-10-22
