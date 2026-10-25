import Instance.AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end Place

section Glued

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

abbrev GluingData (S : Finset (Place K F × Place K F)) : Type _ :=
  Divisor K F × Divisor K F × (↥S → Additive Kˣ)

namespace GluingData

variable {K F}
variable (S : Finset (Place K F × Place K F))

end GluingData


end Glued

end AlgebraicCurve

end
