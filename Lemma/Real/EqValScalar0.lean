import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.coe_val](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {r:ℝ} :
-- imply
  (r:Scalar 0).val = r :=
-- proof
  UnitsSystem.Scalar.coe_val r


-- created on 2026-10-22
