import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.StandardUnit


/--
[StandardUnit.pow'](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {n:ℕ} :
-- imply
  (StandardUnit d:Formal)^n = StandardUnit (n • d) :=
-- proof
  UnitsSystem.StandardUnit.pow' d n


-- created on 2026-10-22
