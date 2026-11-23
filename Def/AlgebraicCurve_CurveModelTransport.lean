import Mathlib
import Def.AlgebraicCurve_CurveModel
import Instance.AlgebraicCurve_CurveModelTransport

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicCurve

section FunctionFieldIso

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

def functionFieldHomOfIso (e : X ≅ Y) : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes (specializes_of_eq (inv_base_genericPoint e)) ≫ e.inv.stalkMap (genericPoint Y)

def functionFieldIsoOfIso (e : X ≅ Y) : X.functionField ≃+* Y.functionField :=
  (asIso (functionFieldHomOfIso e)).commRingCatIsoToRingEquiv

end FunctionFieldIso

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

section ClosedPoints

variable {X Y : Scheme.{u}}

def closedPointsEquivOfIso (e : X ≅ Y) : closedPoints Y ≃ closedPoints X where
  toFun y := ⟨e.inv.base y.1, mem_closedPoints_of_iso e.inv y.2⟩
  invFun x := ⟨e.hom.base x.1, mem_closedPoints_of_iso e.hom x.2⟩
  left_inv y := Subtype.ext (by
    show (e.inv ≫ e.hom).base y.1 = y.1
    rw [e.inv_hom_id]; rfl)
  right_inv x := Subtype.ext (by
    show (e.hom ≫ e.inv).base x.1 = x.1
    rw [e.hom_inv_id]; rfl)

end ClosedPoints

section Transport

variable (Mdl : CurveModel K L) {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) (e : Mdl.C ≅ C)
  (he : e.hom ≫ c = Mdl.toBase)

include he in
def transport : CurveModel K L :=
  letI := isIntegral_of_iso Mdl e
  { C := C
    toBase := c
    isIntegral := isIntegral_of_iso Mdl e
    isProper := isProper_of_iso Mdl c e he
    smooth := smooth_of_iso Mdl c e he
    ffEquiv := Mdl.ffEquiv.trans (functionFieldIsoOfIso e)
    ffEquiv_algebraMap := fun a => by
      rw [RingEquiv.trans_apply, Mdl.ffEquiv_algebraMap]
      exact functionFieldIsoOfIso_baseToFunctionField Mdl.toBase c e he a
    placeOfPoint := fun x => Mdl.placeOfPoint (closedPointsEquivOfIso e x)
    placeOfPoint_bijective := Mdl.placeOfPoint_bijective.comp (closedPointsEquivOfIso e).bijective
    range_stalk_eq := range_stalk_eq_of_iso Mdl e
    finset_subset_affineOpen := fun F => by
end Transport

end CurveModel

end AlgebraicCurve

end
