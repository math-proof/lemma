import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystemExamples
open UnitsSystem
open UnitsSystem.Scalar


/--
[UnitsSystem.Scalar.right_distrib](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystemExamples.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d₁ d₂:Dimensions}
  {a b:Scalar d₁}
  {c:Scalar d₂} :
-- imply
  (a + b) * c = (a * c) + (b * c) :=
-- proof
  UnitsSystem.Scalar.right_distrib a b c


-- created on 2026-10-22
