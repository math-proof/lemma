import Mathlib
set_option maxHeartbeats 800000

open Polynomial IntermediateField

noncomputable section

namespace AlgebraicCurve.KwPke

section PthPowers

variable (F : Type*) [Field F] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP F ℓ]


end PthPowers

section Expansion

variable {F : Type*} [Field F] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

abbrev kw_pke_expansionField (t : F) :
    IntermediateField (kw_pke_pthPowers F ℓ) F :=
  IntermediateField.adjoin (kw_pke_pthPowers F ℓ) {t}

end Expansion

end AlgebraicCurve.KwPke

end
