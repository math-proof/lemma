module

public import Mathlib
public import Structure.ModularCurve_IgusaFunctionField
public import Def.ModularCurve_X1
public import Theorem.UpperHalfPlane.X1

set_option autoImplicit false

public noncomputable section

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
