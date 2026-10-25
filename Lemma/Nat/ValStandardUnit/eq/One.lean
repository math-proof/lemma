import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.StandardUnit


/--
[StandardUnit.val_eq](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions} :
-- imply
  (StandardUnit d).val = 1 :=
-- proof
  UnitsSystem.StandardUnit.val_eq d


-- created on 2026-10-22
