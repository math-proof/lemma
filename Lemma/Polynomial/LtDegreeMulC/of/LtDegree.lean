import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_degree_C_mul_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
