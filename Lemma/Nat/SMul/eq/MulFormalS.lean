import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_smul'](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {c:ℕ}
  {q:Scalar d} :
-- imply
  ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) :=
-- proof
  UnitsSystem.Scalar.toFormal_smul' c q


-- created on 2026-10-22
