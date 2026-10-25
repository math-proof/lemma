import Structure.ModularCurve_ShimuraSubgroup
import Structure.ModularCurve_ShimuraCovering

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Supply

variable (L : Type*) [Field L] [Algebra ℚ L]


end Supply

section Carrier

variable (p : ℕ) [Fact p.Prime]


end Carrier

namespace ShimuraCoveringData

variable {p : ℕ} [Fact p.Prime] (D : ShimuraCoveringData p)


abbrev fieldBar : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) D.field

end ShimuraCoveringData

end ModularCurve

end
