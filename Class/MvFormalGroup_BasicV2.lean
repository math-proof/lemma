import Structure.MvFormalGroup_BasicV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g : ℕ} {R : Type*} [CommRing R]

class IsComm (F : MvFormalGroup g R) : Prop where
  comm : ∀ i,
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
      (F.toPowerSeries i)
      = F.toPowerSeries i

end MvFormalGroup

end
