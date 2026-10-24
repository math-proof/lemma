import Mathlib
import Lemma.Definitions.Def_PresheafOfModules_InternalHom
import Lemma.Definitions.Def_SheafOfModules_MonoidalV2
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesIhomSections

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


end CategoryTheory.MonoidalClosed

noncomputable section

namespace SheafOfModules

open PresheafOfModules PresheafOfModules.InternalHom Functor.Monoidal Functor.LaxMonoidal
  Functor.OplaxMonoidal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

section unit


end unit


end SheafOfModules

end

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}}

section restrict

set_option maxHeartbeats 400000


end restrict

variable (M N : X.Modules)

variable {M N} {P : X.Modules}

variable (M N)

variable {M N}

variable (M N)

variable {M N}

section restrictUnit


end restrictUnit

end AlgebraicGeometry.Scheme.Modules

end
