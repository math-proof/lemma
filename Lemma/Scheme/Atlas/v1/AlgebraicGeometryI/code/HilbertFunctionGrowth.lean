import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.HilbertFunctionGrowth
open Nat MvPolynomial


/--
[pow_le_ascFactorial_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HilbertFunctionGrowth.lean)
-/
@[path]
lemma pow_le_ascFactorial_succ
  {n d : ℕ} :
-- imply
  n ^ d ≤ (n + 1).ascFactorial d := by
-- proof
  induction d with
  | zero => simp [Nat.ascFactorial]
  | succ d ih =>
    rw [pow_succ]
    calc n ^ d * n
      ≤ (n + 1).ascFactorial d * n := Nat.mul_le_mul_right n ih
      _ ≤ (n + 1).ascFactorial d * (n + 1 + d) := Nat.mul_le_mul_left _ (by omega)
      _ = (n + 1 + d) * (n + 1).ascFactorial d := by ring

/--
[pow_le_factorial_mul_choose_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HilbertFunctionGrowth.lean)
-/
@[path]
lemma pow_le_factorial_mul_choose_add
  {n d : ℕ} :
-- imply
  n ^ d ≤ d.factorial * (n + d).choose d := by
-- proof
  calc n ^ d ≤ (n + 1).ascFactorial d := pow_le_ascFactorial_succ n d
    _ = d.factorial * (n + d).choose d := Nat.ascFactorial_eq_factorial_mul_choose n d

/--
[choose_add_le_two_pow_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HilbertFunctionGrowth.lean)
-/
@[path]
lemma choose_add_le_two_pow_mul_pow
  {n d : ℕ}
-- given
  (hnd : d ≤ n) :
-- imply
  (n + d).choose d ≤ 2 ^ d * n ^ d := by
-- proof
  calc (n + d).choose d ≤ (n + d) ^ d := Nat.choose_le_pow _ _
    _ ≤ (2 * n) ^ d := by apply Nat.pow_le_pow_left; omega
    _ = 2 ^ d * n ^ d := by ring


-- created on 2026-10-23
