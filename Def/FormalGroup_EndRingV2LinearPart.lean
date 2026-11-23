-- LinearPart, Unit, End, and linearPartHom material split from
-- Lemma/MvFormalGroup/EndRingV2.lean so the core module can compile
-- without Def.MvFormalGroup_BasicV2 (blocked on the
-- Instance.MvFormalGroup_BasicV2 ↔ Def addMv cycle) or
-- Instance.MvFormalGroup_EndRingV2.

import Def.FormalGroup_EndRingV2
import Def.MvFormalGroup_BasicV2
import Instance.MvFormalGroup_EndRingV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]


def linearPartHom (F : MvFormalGroup g R) [IsComm F] :
    End F →+* Matrix (Fin g) (Fin g) R where
  toFun φ := linearPart (Hom.toPowerSeries φ)
  map_one' := by
    show linearPart (fun i => (X i : MvPowerSeries (Fin g) R)) = 1
    exact linearPart_X
  map_mul' φ ψ := by
    show linearPart (fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i)) = _
    exact linearPart_subst (Hom.constantCoeff_eq_zero ψ) (Hom.toPowerSeries φ)
  map_zero' := by
    show linearPart (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) = 0
    exact linearPart_zero
  map_add' φ ψ := by
    show linearPart (fun i => subst
        (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ)) (F.toPowerSeries i)) = _
    exact linearPart_subst_elim F (Hom.constantCoeff_eq_zero φ)
      (Hom.constantCoeff_eq_zero ψ)

end MvFormalGroup

end
