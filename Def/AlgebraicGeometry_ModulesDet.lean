module
public import Mathlib
public import Instance.PresheafOfModules_ExteriorPower
public import Abbrev.AlgebraicGeometry_ModulesDet
set_option autoImplicit false


public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})


noncomputable def exteriorPower (n : ℕ) : X.Modules ⥤ X.Modules :=
  Modules.toPresheafOfModules X ⋙ presheafExteriorPower X n ⋙
    _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

end AlgebraicGeometry.Scheme.Modules
