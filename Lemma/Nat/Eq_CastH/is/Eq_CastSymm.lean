import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.cast_eq_symm](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
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
  q = q'.cast h ↔ q' = q.cast h.symm :=
-- proof
  UnitsSystem.Scalar.cast_eq_symm q q' h


-- created on 2026-10-22
