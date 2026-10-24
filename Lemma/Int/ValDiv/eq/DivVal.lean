import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_hDiv'''](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d}
  {n:ℤ} :
-- imply
  (q / n).val = q.val / n :=
-- proof
  UnitsSystem.Scalar.val_hDiv''' q n


-- created on 2026-10-22
