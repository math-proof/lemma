import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_le](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {x y:Scalar d} :
-- imply
  x ≤ y ↔ x.val ≤ y.val :=
-- proof
  UnitsSystem.Scalar.val_le x y


-- created on 2026-10-22
