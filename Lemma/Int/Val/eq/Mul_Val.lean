import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_smul''](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {c:ℤ}
  {q:Scalar d} :
-- imply
  (c • q).val = c * q.val :=
-- proof
  UnitsSystem.Scalar.val_smul'' c q


-- created on 2026-10-22
