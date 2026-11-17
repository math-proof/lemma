module

public import Mathlib
public import Structure.ModularCurve_X0

@[expose] public noncomputable section

open IntermediateField

namespace ModularCurve

section Tower

variable (N : ℕ) [NeZero N]

abbrev routeBCoordRing : Subalgebra (Polynomial ℤ) (modularFunctionField N) :=
  integralClosure (Polynomial ℤ) (modularFunctionField N)

end Tower

end ModularCurve

end
