import Mathlib

set_option maxHeartbeats 800000

open Polynomial IntermediateField

noncomputable section

namespace AlgebraicCurve.KwPke


section PthPowers

variable (F : Type*) [Field F] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP F ℓ]

def kw_pke_pthPowers : Subfield F := (frobenius F ℓ).fieldRange

end PthPowers

end AlgebraicCurve.KwPke

end
