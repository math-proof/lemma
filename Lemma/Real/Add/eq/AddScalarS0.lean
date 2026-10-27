import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.coe_add](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {r s:ℝ} :
-- imply
  ((r+s:ℝ):Scalar 0) = (r:Scalar 0) + (s:Scalar 0) :=
-- proof
  UnitsSystem.Scalar.coe_add r s


-- created on 2026-10-22
