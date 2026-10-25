import Mathlib

set_option autoImplicit false

universe u v

noncomputable section

open MvPolynomial

namespace WeierstrassCurve.Generic

section CommRing

variable (K : Type u) [CommRing K]

section coeffs

variable {A : Type v}

end coeffs

end CommRing

section Field

variable (K : Type u) [Field K]

abbrev FunctionField : Type u := FractionRing (MvPolynomial (Fin 5) K)

abbrev Closure : Type u := AlgebraicClosure (FunctionField K)

end Field

end WeierstrassCurve.Generic

end
