import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyRowDerivative_derivativeRow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K]
  (f : Fin k → K[X])
  (n : ℕ) :
-- imply
  rothPolyRowDerivative (rothPolyDerivativeRow f n) = rothPolyDerivativeRow f (n + 1) := by
-- proof
  ext j
  simp only [rothPolyRowDerivative, rothPolyDerivativeRow]
  rw [Function.iterate_succ_apply']


-- created on 2026-10-21
