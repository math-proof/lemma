module

public import Class.MvFormalGroup_BasicV2
public import Theorem.MvPowerSeries.EndRingV2Subst
public import Def.FormalGroup_EndRingV2

public noncomputable section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}


@[simp]
public theorem toPowerSeries_zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) :
    (Hom.zero F G).toPowerSeries = fun _ => 0 := rfl


@[simp]
public theorem toPowerSeries_add [IsComm G] (φ ψ : Hom F G) :
    (Hom.add φ ψ).toPowerSeries
      = fun i => subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i) :=
  rfl


end Hom

end MvFormalGroup
