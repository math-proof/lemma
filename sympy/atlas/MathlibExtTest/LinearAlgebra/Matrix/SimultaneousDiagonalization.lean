/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean -/


import Mathlib.Algebra.Order.Star.Real
import Lemma.Matrix.SimultaneousDiagonalization

open MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

-- Congruence normalization gives the expected determinant identity.
example {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P.PosDef) : ∃ Q : Matrix n n ℝ, Q.det ^ 2 * P.det = 1 := by
  obtain ⟨Q, _, hcongr⟩ := hP.exists_isUnit_transpose_mul_mul_eq_one
  refine ⟨Q, ?_⟩
  have hdet : Q.det * P.det * Q.det = 1 := by
    simpa [Matrix.det_mul] using congrArg Matrix.det hcongr
  calc
    Q.det ^ 2 * P.det = Q.det * P.det * Q.det := by ring
    _ = 1 := hdet

-- With the identity metric, the simultaneous congruence is orthogonal and nonsingular.
example (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsSymm) :
    ∃ C : Matrix (Fin 2) (Fin 2) ℝ,
      C.det ≠ 0 ∧ (Matrix.transpose C * S * C).IsDiag ∧ Matrix.transpose C * C = 1 := by
  obtain ⟨C, hC, hdiag, horth⟩ :=
    simultaneous_diagonalization_posDef S 1 hS Matrix.PosDef.one
  refine ⟨C, ?_, hdiag, ?_⟩
  · exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det C).mp hC)
  · simpa using horth
