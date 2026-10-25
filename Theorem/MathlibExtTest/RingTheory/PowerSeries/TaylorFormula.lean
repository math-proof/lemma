/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/PowerSeries/TaylorFormula.lean -/

-- Author: @toskua, Avocado

import Lemma.PowerSeries.TaylorFormula


namespace PowerSeriesTaylorFormulaTest

/-- Compile-time consumer of the public Taylor identity. -/
example {R : Type*} [CommRing R] [Algebra ℚ R] (f : PowerSeries R) :
    (fun d : Fin 2 →₀ ℕ =>
      ((d 1).factorial : ℚ)⁻¹ •
        PowerSeries.coeff (d 0) (((PowerSeries.derivative)^[d 1]) f)) =
      MvPowerSeries.subst
        (fun _ : Unit =>
          MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) f :=
  PowerSeries.taylorFormula f

end PowerSeriesTaylorFormulaTest
