import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_smul](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {α} [SMul α ℝ]
  {d:Dimensions}
  {a : α}
  {q:Scalar d} :
-- imply
  (a • q).val = a • q.val :=
-- proof
  UnitsSystem.Scalar.val_smul a q


-- created on 2026-10-22
