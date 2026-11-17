module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyRowDerivative_derivativeRow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Polynomial.RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1
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
-- updated on 2026-11-13
