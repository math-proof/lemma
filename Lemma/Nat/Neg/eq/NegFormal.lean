import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_neg](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d} :
-- imply
  ((-q:Scalar d):Formal) = -(q:Formal) :=
-- proof
  UnitsSystem.Scalar.toFormal_neg q


-- created on 2026-10-22
