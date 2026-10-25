-- Carved from Lemma/Definitions/Def_PresheafOfModules_InternalHom.lean: instance decls only.
import Mathlib
import Lemma.PresheafOfModules.InternalHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

section general

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace InternalHom

variable {F N}

instance (X : Cᵒᵖ) : SMul (R.obj X) (naturalFamilies F N X) where
  smul r φ := ⟨fun Y f => R.map f r • φ.1 f, by
    intro Y Z f g x
    simp only [LinearMap.smul_apply]
    rw [N.map_smul]
    erw [φ.2 f g x]
    congr 1
    rw [Functor.map_comp]
    rfl⟩

instance (X : Cᵒᵖ) : Module (R.obj X) (naturalFamilies F N X) where
  one_smul φ := by ext Y f x; simp
  mul_smul r s φ := by ext Y f x; simp [mul_smul]
  smul_zero r := by ext Y f x; simp
  smul_add r φ ψ := by ext Y f x; simp
  add_smul r s φ := by ext Y f x; simp [add_smul]
  zero_smul φ := by ext Y f x; simp

variable (F N)

instance (X : Cᵒᵖ) : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((presheaf F N).obj X) :=
  inferInstanceAs (Module (R.obj X) (naturalFamilies F N X))

end InternalHom

open InternalHom

end general

section closed

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}


open InternalHom

noncomputable instance instMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  closed F := { rightAdj := ihomFunctor F, adj := tensorIhomAdj F }

end closed

end PresheafOfModules
