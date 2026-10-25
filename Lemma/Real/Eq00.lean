import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Formal


/--
[Formal.coe_zero](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem] :
-- imply
  ((0:ℝ):Formal) = 0 :=
-- proof
  UnitsSystem.Formal.coe_zero


-- created on 2026-10-22
