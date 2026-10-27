import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_lt](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {x y:Scalar d} :
-- imply
  x < y ↔ x.val < y.val :=
-- proof
  UnitsSystem.Scalar.val_lt x y


-- created on 2026-10-22
