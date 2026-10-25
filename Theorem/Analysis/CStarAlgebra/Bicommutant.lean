import Mathlib.Analysis.InnerProductSpace.Adjoint
import Def.Analysis.CStarAlgebra.Bicommutant


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Star on matrices corresponds to adjoint on operators. -/
theorem matToOp_star (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    matToOp n (star A) = LinearMap.adjoint (matToOp n A) := by
  have h1 : star A = Aᴴ := Matrix.star_eq_conjTranspose A
  rw [h1]
  change Matrix.toEuclideanLin Aᴴ = LinearMap.adjoint (Matrix.toEuclideanLin A)
  exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

/-- `matToOp` preserves multiplication. -/
theorem matToOp_mul (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    matToOp n (A * B) = matToOp n A * matToOp n B := by
  unfold matToOp
  rw [Matrix.toLpLin_mul, Module.End.mul_eq_comp]

/-- `matToOp` is injective. -/
theorem matToOp_injective (n : ℕ) : Function.Injective (matToOp n) :=
  Matrix.toEuclideanLin.injective

end Complex.CStarAlgebra.Bicommutant
