import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.neZero_iff](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d} :
-- imply
  NeZero q ↔ q.val ≠ 0 :=
-- proof
  UnitsSystem.Scalar.neZero_iff q


-- created on 2026-10-22
