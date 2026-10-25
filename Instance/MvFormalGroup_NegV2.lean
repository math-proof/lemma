-- Carved from Lemma/Definitions/Def_MvFormalGroup_NegV2.lean: instance decls only.
import Instance.MvFormalGroup_EndRingV2
import Lemma.MvFormalGroup.NegV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]


namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

instance instNeg [IsComm G] : Neg (Hom F G) := ⟨Hom.neg⟩

instance instAddCommGroup [IsComm G] : AddCommGroup (Hom F G) :=
  { Hom.instAddCommMonoid with
    neg := Hom.neg
    zsmul := zsmulRec
    neg_add_cancel := fun φ => by
      apply Hom.ext
      funext i
      show subst (Sum.elim (negSeries G φ.toPowerSeries) φ.toPowerSeries)
          (G.toPowerSeries i) = 0
      exact subst_elim_negSeries_left G φ.constantCoeff_eq_zero i }

end Hom

namespace End

variable (F : MvFormalGroup g R)

instance instAddCommGroup [IsComm F] : AddCommGroup (End F) :=
  inferInstanceAs (AddCommGroup (Hom F F))

instance instRing [IsComm F] : Ring (End F) :=
  { End.instSemiring F, End.instAddCommGroup F with }

end End


end MvFormalGroup
end
