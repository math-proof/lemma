import Mathlib
import Structure.AlgebraicCurve_Place
import Structure.AlgebraicCurve_LocalResidue

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}
variable (v : Place K F)


def dCoord : Ω[F⁄K] := KaehlerDifferential.D K F v.uniformizer


def differentialCoeff (ω : Ω[F⁄K]) : F :=
  let := Classical.propDecidable
  if h : ∃ f : F, ω = f • v.dCoord then h.choose else 0




def ordDifferential (ω : Ω[F⁄K]) : ℤ := v.ord (v.differentialCoeff ω)


end Place

end AlgebraicCurve

end
