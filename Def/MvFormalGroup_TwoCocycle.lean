import Mathlib
import Class.MvFormalGroup_BasicV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {n : ℕ} {R : Type*} [CommRing R]

def addCoboundary (F : MvFormalGroup n R) (g : MvPowerSeries (Fin n) R) :
    MvPowerSeries (Fin n ⊕ Fin n) R :=
  subst F.toPowerSeries g
    - subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R)) g
    - subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) R)) g

end MvFormalGroup

end
