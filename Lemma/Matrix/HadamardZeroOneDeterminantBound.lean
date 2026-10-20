import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.HadamardZeroOneDeterminantBound
open Matrix
open MetaMathlibExt


/--
[hadamard_zero_one_determinant_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/HadamardZeroOneDeterminantBound.lean)
-/
@[path]
private lemma hadamard_zero_one_determinant_bound_eq
  {n : ℕ}
  {B : Matrix (Fin n) (Fin n) ℝ}
-- given
  (hn : 0 < n)
  (hB : ∀ i j, B i j = 0 ∨ B i j = 1) :
-- imply
  |B.det| ≤ ((2 : ℝ)⁻¹) ^ n *
    Real.rpow ((n : ℝ) + 1) (((n : ℝ) + 1) / 2) := by
-- proof
  apply MetaMathlibExt.hadamard_zero_one_determinant_bound n B hn hB


-- created on 2026-10-20
