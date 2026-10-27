import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_hMul](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d₁ d₂:Dimensions}
  {q₁:Scalar d₁}
  {q₂:Scalar d₂} :
-- imply
  ((q₁ * q₂:Scalar _):Formal) = (q₁:Formal) * (q₂:Formal) :=
-- proof
  UnitsSystem.Scalar.toFormal_hMul q₁ q₂


-- created on 2026-10-22
