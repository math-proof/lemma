import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.in_def](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {unit q:Scalar d} [h: NeZero unit] :
-- imply
  q = (unit.in q) • unit :=
-- proof
  UnitsSystem.Scalar.in_def unit q


-- created on 2026-10-22
