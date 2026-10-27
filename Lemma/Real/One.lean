import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Formal


/--
[Formal.coe_one](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem] :
-- imply
  ((1:ℝ):Formal) = 1 :=
-- proof
  UnitsSystem.Formal.coe_one


-- created on 2026-10-22
