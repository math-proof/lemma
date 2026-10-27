import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.cast_val](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d d':Dimensions}
  {q: Scalar d}
-- given
  (h: d' = d := by module) :
-- imply
  (q.cast h).val = q.val :=
-- proof
  UnitsSystem.Scalar.cast_val q h


-- created on 2026-10-22
