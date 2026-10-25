import Mathlib
import Lemma.PresheafOfModules.ExteriorPower
import Abbrev.AlgebraicGeometry_ModulesDet
import Def.AlgebraicGeometry_ModulesDet

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})


variable {X} in
@[simp] lemma exteriorPower_obj (n : ℕ) (M : X.Modules) :
    (exteriorPower X n).obj M =
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((presheafExteriorPower X n).obj M.val) := rfl

end AlgebraicGeometry.Scheme.Modules
