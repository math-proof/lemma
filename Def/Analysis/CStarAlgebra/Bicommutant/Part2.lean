import Mathlib.Analysis.InnerProductSpace.Adjoint
import Theorem.Analysis.CStarAlgebra.Bicommutant


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Amplified block-diagonal action on `m` copies of Euclidean space. -/
noncomputable def ampOp (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    (LinearMap.pi fun i => (matToOp n A).comp (PiLp.projₗ 2 _ i))

end Complex.CStarAlgebra.Bicommutant
