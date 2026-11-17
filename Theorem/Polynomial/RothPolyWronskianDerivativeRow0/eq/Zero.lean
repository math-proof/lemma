module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyWronskianDerivativeRow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Polynomial.RothPolyWronskianDerivativeRow0.eq.Zero
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
-- updated on 2026-11-13
