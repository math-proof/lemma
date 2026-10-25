import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

section general

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

namespace InternalHom

abbrev PiFamily (X : Cᵒᵖ) : Type (max u u' v') :=
  ∀ ⦃Y : Cᵒᵖ⦄ (_ : X ⟶ Y), (F.obj Y →ₗ[R.obj Y] N.obj Y)

end InternalHom

open InternalHom

end general

section closed

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

namespace InternalHom

end InternalHom

open InternalHom

end closed

end PresheafOfModules
