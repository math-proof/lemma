import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.HadamardDeterminant
open Finset Matrix BigOperators
open InnerProductSpace
open scoped InnerProductSpace
open MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant


/--
[hadamard_determinant_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/HadamardDeterminant.lean)
-/
@[path]
private lemma hadamard_determinant_inequality_eq
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ} :
-- imply
  ‖A.det‖ ≤ ∏ i : Fin n, Real.sqrt (∑ j : Fin n, Complex.normSq (A i j)) := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant.hadamard_determinant_inequality A


-- created on 2026-10-20
