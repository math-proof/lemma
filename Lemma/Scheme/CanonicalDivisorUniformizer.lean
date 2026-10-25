import Mathlib
import Class.ModularCurve_CanonicalDivisor
import Structure.AlgebraicCurve_LocalResidue

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

end Place

end AlgebraicCurve

end
