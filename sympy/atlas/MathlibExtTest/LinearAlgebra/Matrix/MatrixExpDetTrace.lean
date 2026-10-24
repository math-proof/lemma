/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/MatrixExpDetTrace.lean -/


import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import sympy.atlas.LinearAlgebra.Matrix.MatrixExpDetTrace
import Lemma.Matrix.MatrixExpDetTrace

open MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

-- A trace-zero matrix has determinant-one exponential.
example (A : Matrix n n ℂ) (hA : Matrix.trace A = 0) :
    Matrix.det (NormedSpace.exp A) = 1 := by
  rw [matrix_det_exp_eq_exp_trace, hA, Complex.exp_zero]

-- The exponential of a nilpotent `A` commutes with every matrix that commutes with `A`.
example (A B : Matrix n n ℂ) (hA : IsNilpotent A) (hAB : Commute A B) :
    Commute (NormedSpace.exp A) B := by
  obtain ⟨m, hm⟩ := matrix_exp_eq_sum_of_isNilpotent A hA
  rw [hm]
  apply Commute.sum_left
  intro k _
  exact (hAB.pow_left k).smul_left ((Nat.factorial k : ℂ)⁻¹)

-- A nilpotent matrix has determinant-one exponential.
example (N : Matrix n n ℂ) (hN : IsNilpotent N) :
    Matrix.det (NormedSpace.exp N) = 1 := by
  have htrace : Matrix.trace N = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [matrix_det_exp_eq_exp_trace, htrace, Complex.exp_zero]
