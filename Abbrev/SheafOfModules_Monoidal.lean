import Mathlib
import Instance.PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

abbrev ringSheaf : Sheaf J RingCat.{u} := ⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩

abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev sheafifyFunctor : PMod 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev toPMod : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) ⥤ PMod 𝒪 :=
  SheafOfModules.forget (ringSheaf 𝒪 h𝒪) ⋙
    PresheafOfModules.restrictScalars (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))


end SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u})


abbrev Scheme.Modules.tensor (L M : X.Modules) : X.Modules := L ⊗ M

abbrev Scheme.Modules.dual (L : X.Modules) : X.Modules := (ihom L).obj (𝟙_ X.Modules)

variable (X) in

abbrev Scheme.Modules.sheafify : X.PresheafOfModules ⥤ X.Modules :=
  SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property


end AlgebraicGeometry

end
