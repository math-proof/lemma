import Mathlib.Analysis.InnerProductSpace.Adjoint
import Theorem.Analysis.CStarAlgebra.Bicommutant.Part3


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- The `(i, j)` entry of an amplified operator, as an operator on one copy. -/
noncomputable def ampEntry (n m : ℕ)
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) (i j : Fin m) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i).comp
    (T.comp (ampIncl n m j))

/-- The matrix realizing an entry operator. -/
noncomputable def entryMat (n : ℕ)
    (E : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.toEuclideanLin.symm E

end Complex.CStarAlgebra.Bicommutant
