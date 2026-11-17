module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_degree_C_mul_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Polynomial.LtDegreeMulC.of.LtDegree
  {P : ℤ[X]} {d : ℕ}
  (c : ℤ)
-- given
  (hP : P.degree < d) :
-- imply
  (C c * P).degree < d := by
-- proof
  if hc : c = 0 then
    simp [hc]
  else
    rwa [degree_C_mul hc]


-- created on 2026-10-21
-- updated on 2026-11-13
