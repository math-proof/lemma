import Mathlib
import Class.ModularCurve_CanonicalDivisor
import Class.AlgebraicCurve_CanonicalDivisor
import Def.AlgebraicCurve_CanonicalDivisor

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) :
    canonicalDivisorOf hω v = v.ordDifferential ω :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose_spec v

end AlgebraicCurve

end
