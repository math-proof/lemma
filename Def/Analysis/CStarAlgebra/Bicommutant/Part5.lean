import Mathlib.Analysis.InnerProductSpace.Adjoint
import Theorem.Analysis.CStarAlgebra.Bicommutant.Part4


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Cyclic vector with standard-basis components. -/
noncomputable def cycVec (n : ℕ) :
    PiLp 2 (fun _ : Fin n => EuclideanSpace ℂ (Fin n)) :=
  WithLp.toLp 2 (fun j => WithLp.toLp 2
    (Pi.single (M := fun _ : Fin n => ℂ) j 1))

end Complex.CStarAlgebra.Bicommutant
