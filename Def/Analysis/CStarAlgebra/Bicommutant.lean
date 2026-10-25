import Mathlib.Analysis.InnerProductSpace.Adjoint


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Matrix as an operator on Euclidean space, via the `toLp` algebra equivalence. -/
noncomputable def matToOp (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanLin A

end Complex.CStarAlgebra.Bicommutant
