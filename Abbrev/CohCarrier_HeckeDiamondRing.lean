import Lemma.CohCarrier.Inst

set_option autoImplicit false

noncomputable section

namespace CohCarrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (H' : Subgroup (ZMod M)ˣ)
  (A : Type) [CommRing A]

abbrev GoodPrime : Type := {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M}


end CohCarrier

end
