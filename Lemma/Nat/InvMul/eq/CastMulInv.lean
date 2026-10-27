import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.pow_inv](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d}
  {n:ℕ} :
-- imply
  (q ** n).inv = (q.inv ** n).cast :=
-- proof
  UnitsSystem.Scalar.pow_inv q n


-- created on 2026-10-22
