import Mathlib
import Def.AlgebraicGeometry_ModulesPushforwardRestrict

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)


lemma pushforwardRestrictIso_hom_app_app (M : X.Modules) (U : W.toScheme.Opens) :
    ((pushforwardRestrictIso g W).hom.app M).app U =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage g W U).symm).op := by
  first
    | rfl
    | (ext x; simp [pushforwardRestrictIso, restrictPushforwardOpensIso, SheafOfModules.pushforwardCongr,
        SheafOfModules.pushforwardNatIso, SheafOfModules.pushforwardComp, eqToHom_op, Scheme.Modules.Hom.app])

end AlgebraicGeometry.Scheme.Modules
