import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystemExamples
open UnitsSystem
open UnitsSystem.Scalar


/--
[UnitsSystem.Scalar.sq_add](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystemExamples.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {a b:Scalar d} :
-- imply
  (a+b)**2 = a**2 + (2 • a * b).cast + b**2 :=
-- proof
  UnitsSystem.Scalar.sq_add a b


-- created on 2026-10-22
