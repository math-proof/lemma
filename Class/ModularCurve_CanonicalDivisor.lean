import Def.ModularCurve_CanonicalDivisor

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F)

class DCoordGenerates : Prop where
  span_eq_top : Submodule.span F {v.dCoord} = ⊤

end Place
end AlgebraicCurve
