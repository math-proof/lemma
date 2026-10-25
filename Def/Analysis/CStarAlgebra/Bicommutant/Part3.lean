import Mathlib.Analysis.InnerProductSpace.Adjoint
import Theorem.Analysis.CStarAlgebra.Bicommutant.Part2


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Inclusion of one copy into the amplified space. -/
noncomputable def ampIncl (n m : ℕ) (j : Fin m) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :=
  (WithLp.linearEquiv 2 ℂ (∀ _ : Fin m, EuclideanSpace ℂ (Fin n))).symm.toLinearMap.comp
    (LinearMap.single ℂ (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j)

end Complex.CStarAlgebra.Bicommutant
