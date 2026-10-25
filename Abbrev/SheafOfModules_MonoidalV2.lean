import Mathlib
import Instance.PresheafOfModules_InternalHom
import Instance.SheafOfModules_Monoidal

section InlinedTheorems

section LinkageInlined_5b3a613b

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite

noncomputable section

namespace PresheafOfModules

namespace InternalHom

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))


private abbrev appAt {X : Cᵒᵖ} (s : (presheafHom F.presheaf N.presheaf).obj X) (Y : (Over X.unop)ᵒᵖ)
    (x : F.obj (Opposite.op Y.unop.left)) : N.obj (Opposite.op Y.unop.left) :=
  s.app Y x


end InternalHom

end PresheafOfModules

end


end LinkageInlined_5b3a613b

section LinkageInlined_68107509

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace PresheafOfModules.IsMonoidalW

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
  (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

private abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

private abbrev W : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

private abbrev shf : PMod 𝒪 ⥤ SheafOfModules.{u} R := PresheafOfModules.sheafification α

private abbrev inc : SheafOfModules.{u} R ⥤ PMod 𝒪 :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α

private abbrev adj : shf 𝒪 R α ⊣ inc 𝒪 R α := PresheafOfModules.sheafificationAdjunction α

private local instance : (inc 𝒪 R α).Faithful := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.faithful
private local instance : (inc 𝒪 R α).Full := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.full


end PresheafOfModules.IsMonoidalW

end

open PresheafOfModules.IsMonoidalW in


end LinkageInlined_68107509

end InlinedTheorems

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]


end SheafOfModules

namespace AlgebraicGeometry


end AlgebraicGeometry

end
