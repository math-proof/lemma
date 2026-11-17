module

public import Def.ModularCurve_CanonicalDivisor
public import Class.AlgebraicCurve_DivisorClassGroup

public section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

class HasCanonicalDivisor : Prop where
  exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,
    ∀ v : Place K F, D v = v.ordDifferential ω

end AlgebraicCurve
