import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystemExamples
open UnitsSystem
open UnitsSystem.Scalar


/--
[UnitsSystem.Scalar.hMul_assoc](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystemExamples.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d₁ d₂ d₃:Dimensions}
  {a:Scalar d₁}
  {b:Scalar d₂}
  {c:Scalar d₃} :
-- imply
  a * (b * c) = ((a * b) * c).cast :=
-- proof
  UnitsSystem.Scalar.hMul_assoc a b c


-- created on 2026-10-22
