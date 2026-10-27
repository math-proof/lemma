import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_cast](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d d': Dimensions}
  {q:Scalar d}
-- given
  (h:d' = d := by module) :
-- imply
  ((q.cast h):Formal) = (q:Formal) :=
-- proof
  UnitsSystem.Scalar.toFormal_cast q h


-- created on 2026-10-22
