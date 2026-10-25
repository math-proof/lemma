-- Carved from Lemma/Definitions/Def_PresheafOfModules_ExteriorPower.lean: instance decls only.
import Mathlib
import Lemma.PresheafOfModules.ExteriorPower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory
namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))


noncomputable instance instModulePresheafAb (X : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((presheafAb n M).obj X) :=
  inferInstanceAs (Module (R.obj X) (⋀[R.obj X]^n (M.obj X)))

end ExteriorPower

end PresheafOfModules

