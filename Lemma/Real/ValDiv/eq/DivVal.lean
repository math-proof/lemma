import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_hDiv'](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d}
  {r:ℝ} :
-- imply
  (q / r).val = q.val / r :=
-- proof
  UnitsSystem.Scalar.val_hDiv' q r


-- created on 2026-10-22
