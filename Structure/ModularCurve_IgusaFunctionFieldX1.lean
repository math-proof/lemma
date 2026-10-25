import Mathlib
import Structure.ModularCurve_IgusaFunctionField
import Lemma.ModularCurve.X1

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve

variable (κ : Type*) [Field κ] (M : ℕ)

structure IntegralWeightOneForm where

  form : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 1

  series : PowerSeries ℤ
  isIntegralQExp : IsIntegralQExp form series

  intSeriesC_ne_zero : intSeriesC κ series ≠ 0

variable {κ M}


variable (κ M)


end ModularCurve

end
