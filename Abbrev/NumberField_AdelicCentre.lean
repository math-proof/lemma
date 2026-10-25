import Instance.NumberField_AdelicHaar
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

open IsDedekindDomain NumberField MeasureTheory
open scoped Pointwise

noncomputable section

namespace NumberField.AdelicCentre

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicPGL2 : Type _ :=
  GL (Fin 2) (AdeleRing R K) ⧸ Subgroup.center (GL (Fin 2) (AdeleRing R K))

section NumberFieldCase

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]


end NumberFieldCase

end NumberField.AdelicCentre

end
