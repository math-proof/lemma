module

public import Structure.HeckeGalois_EichlerShimura
public import Instance.ModularCurve_ArithmeticGalois

set_option autoImplicit false

@[expose] public noncomputable section

namespace ModularCurve

section ConcreteCitation

variable (N p : ℕ) [NeZero N]
variable [Module HeckeAlg (JZero N)]

abbrev UnramifiedOutsideConcrete : Prop :=
  UnramifiedOutside (K := ℚ) (L := AlgebraicClosure ℚ) N p (JZero N)

abbrev FrobeniusQuadraticConcrete : Prop :=
  FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p (JZero N)

end ConcreteCitation

end ModularCurve

end
