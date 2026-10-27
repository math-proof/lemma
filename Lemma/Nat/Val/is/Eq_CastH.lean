import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.cast_eq](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d d':Dimensions}
  {q: Scalar d}
  {q': Scalar d'}
-- given
  (h: d = d' := by module) :
-- imply
  q.val = q'.val ↔ q = q'.cast h :=
-- proof
  UnitsSystem.Scalar.cast_eq q q' h


-- created on 2026-10-22
