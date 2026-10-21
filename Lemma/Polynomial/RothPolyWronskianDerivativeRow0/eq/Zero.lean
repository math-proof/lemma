import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyWronskianDerivativeRow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K]
  (f : Fin (k + 1) → K[X])
  (n : ℕ) :
-- imply
  rothPolyWronskianDerivativeRow f n 0 = 0 := by
-- proof
  change (derivative^[n]) (wronskian (f 0) (f 0)) = 0
  rw [wronskian_self_eq_zero]
  simp


-- created on 2026-10-21
