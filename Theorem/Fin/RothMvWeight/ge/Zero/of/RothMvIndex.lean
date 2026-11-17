module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvWeight.ge.Zero.of.RothMvIndex
  {m : ℕ}
  (r : Fin m → ℕ) (i : RothMvIndex m) :
-- imply
  0 ≤ rothMvWeight r i := by
-- proof
  unfold rothMvWeight
  positivity


-- updated on 2026-11-13
-- created on 2026-10-21
