module

public import Theorem.MvPowerSeries.EndRingV2
public import Theorem.MvPowerSeries.NegV2Subst
public import Def.FormalGroup_NegV2

public noncomputable section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}


@[simp]
public theorem toPowerSeries_neg [IsComm G] (φ : Hom F G) :
    (Hom.neg φ).toPowerSeries = negSeries G φ.toPowerSeries := rfl


@[simp]
public theorem toPowerSeries_sub [IsComm G] (φ ψ : Hom F G) :
    (Hom.add φ (Hom.neg ψ)).toPowerSeries = fun i =>
      subst (Sum.elim φ.toPowerSeries (negSeries G ψ.toPowerSeries))
        (G.toPowerSeries i) := rfl

end Hom

end MvFormalGroup
