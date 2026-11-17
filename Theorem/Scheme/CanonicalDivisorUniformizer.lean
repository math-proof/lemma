module

public import Mathlib
public import Class.ModularCurve_CanonicalDivisor
public import Structure.AlgebraicCurve_LocalResidue

public noncomputable section

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

public theorem dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

end Place

end AlgebraicCurve

end
