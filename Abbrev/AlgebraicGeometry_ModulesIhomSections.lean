import Mathlib
import Instance.PresheafOfModules_InternalHom
import Instance.SheafOfModules_Monoidal
import Lemma.AlgebraicGeometry.ModulesSectionsTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace PresheafOfModules

namespace InternalHom

namespace IsSheafAux

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

variable {F N} in

abbrev appAt {X : Cᵒᵖ} (s : (presheafHom F.presheaf N.presheaf).obj X) (Y : (Over X.unop)ᵒᵖ)
    (x : F.obj (Opposite.op Y.unop.left)) : N.obj (Opposite.op Y.unop.left) :=
  s.app Y x

end IsSheafAux

end InternalHom

end PresheafOfModules

end

noncomputable section

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

end PresheafOfModules

end

namespace CategoryTheory.MonoidalClosed

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [MonoidalClosed C]

end CategoryTheory.MonoidalClosed

noncomputable section

namespace SheafOfModules

open PresheafOfModules PresheafOfModules.InternalHom Functor.Monoidal Functor.LaxMonoidal
  Functor.OplaxMonoidal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

section unit

variable {𝒪 h𝒪}

end unit

variable (M N : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

abbrev ihomModel : PMod 𝒪 :=
  PresheafOfModules.ihomObj ((toPMod 𝒪 h𝒪).obj M) ((toPMod 𝒪 h𝒪).obj N)

end SheafOfModules

end

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}}

variable (X) in

abbrev toPMod : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

section restrict

set_option maxHeartbeats 400000

variable (U : X.Opens)

abbrev opHomImage (W : (U : Scheme.{u}).Opens) : Opposite.op U ⟶ Opposite.op (U.ι ''ᵁ W) :=
  (homOfLE (U.ι_image_le W)).op

end restrict

variable (M N : X.Modules)

section restrictUnit

variable {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

end restrictUnit

end AlgebraicGeometry.Scheme.Modules

end
