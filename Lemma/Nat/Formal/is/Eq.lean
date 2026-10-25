import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_inj](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d: Dimensions}
  {q₁ q₂:Scalar d} :
-- imply
  (q₁:Formal) = (q₂:Formal) ↔ q₁ = q₂ :=
-- proof
  UnitsSystem.Scalar.toFormal_inj q₁ q₂


-- created on 2026-10-22
