import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_hDiv'''](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q:Scalar d}
  {n:ℤ} :
-- imply
  ((q / n:Scalar _):Formal) = (q:Formal) * (((n:ℝ)⁻¹:ℝ):Formal) :=
-- proof
  UnitsSystem.Scalar.toFormal_hDiv''' q n


-- created on 2026-10-22
