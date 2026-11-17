module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_isPrimitive_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Polynomial.IsPrimitivePow.of.IsPrimitive
  (P : ℤ[X])
  (k : ℕ)
-- given
  (hP : P.IsPrimitive) :
-- imply
  (P ^ k).IsPrimitive := by
-- proof
  induction k with
  | zero =>
    simp [pow_zero]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul hP


-- created on 2026-10-21
-- updated on 2026-11-13
