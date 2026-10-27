import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_in](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {unit q:Scalar d} :
-- imply
  unit.in q = q.val / unit.val :=
-- proof
  UnitsSystem.Scalar.val_in d unit q


-- created on 2026-10-22
