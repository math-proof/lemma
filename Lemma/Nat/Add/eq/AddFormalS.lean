import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_add](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q₁ q₂:Scalar d} :
-- imply
  ((q₁ + q₂:Scalar d):Formal) = (q₁:Formal) + (q₂:Formal) :=
-- proof
  UnitsSystem.Scalar.toFormal_add q₁ q₂


-- created on 2026-10-22
