-- Carved from Lemma/Definitions/Def_ModularCurve_PhiGen.lean: instance decls only.
import Lemma.ModularCurve.X0
import Lemma.ModularCurve.LaurentCoeff
import Mathlib.Algebra.Polynomial.BigOperators
import Lemma.ModularCurve.PhiGen

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology
open PowerSeries HahnSeries IntermediateField Polynomial

namespace ModularCurve


namespace PhiGen

section CosetIndex

variable (ℓ : ℕ)

instance instNeZeroPhiGenCosetA [hℓ : Fact (Nat.Prime ℓ)] (i : Fin (ℓ + 1)) :
    NeZero (cosetA ℓ i) :=
  ⟨by unfold cosetA; split <;> simp [hℓ.out.ne_zero]⟩

end CosetIndex


end PhiGen

end ModularCurve
end
