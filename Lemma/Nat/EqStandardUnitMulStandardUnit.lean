import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.StandardUnit


/--
[StandardUnit.mul'](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d₁ d₂:Dimensions} :
-- imply
  (StandardUnit d₁:Formal) * (StandardUnit d₂:Formal) = StandardUnit (d₁+d₂) :=
-- proof
  UnitsSystem.StandardUnit.mul' d₁ d₂


-- created on 2026-10-22
