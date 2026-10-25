import Mathlib.Analysis.InnerProductSpace.Adjoint
import Def.Analysis.CStarAlgebra.Bicommutant.Part5


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

theorem cycVec_ofLp (n : ℕ) (j : Fin n) :
    (cycVec n).ofLp j =
      WithLp.toLp 2 (Pi.single (M := fun _ : Fin n => ℂ) j 1) :=
  rfl

end Complex.CStarAlgebra.Bicommutant
