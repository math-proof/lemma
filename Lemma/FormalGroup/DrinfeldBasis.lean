import Mathlib
import Lemma.FormalGroup.NSeries
import Def.FormalGroup_DrinfeldBasis
import Structure.FormalGroup_DrinfeldBasis

set_option autoImplicit false

noncomputable section

namespace FormalGroup

variable {T : Type*} [CommRing T] [UniformSpace T]


section Adic

variable {T : Type*} [CommRing T]


theorem isDrinfeldBasisAdic_iff (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) :
    F.IsDrinfeldBasisAdic I q x₀ x₁ ↔
      ∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * F.drinfeldDivisorAdic I q x₀ x₁ :=
  Iff.rfl

end Adic

end FormalGroup

end
