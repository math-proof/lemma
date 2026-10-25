import Mathlib
import Def.ModularCurve_JqCoeff
import Instance.AlgebraicCurve_RatFuncPlaces

namespace ModularCurve
end ModularCurve

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Transcendence

variable (K : Type*) [Field K]

end Transcendence

section Jacobian

variable (K : Type*) [Field K]

abbrev charLJacobian (N : ℕ) [NeZero N] : Type _ :=
  Pic0 K (modularFunctionFieldC K N)

end Jacobian

section Map

variable {K k : Type*} [Field K] [Field k]

end Map

section Degree

variable {K k : Type*} [Field K] [Field k]

end Degree

section Galois

variable {K k : Type*} [Field K] [Field k]

end Galois

end ModularCurve

end
