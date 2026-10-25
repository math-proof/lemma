import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Structure.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelSubPicPresheaf
import Def.AlgebraicGeometry_RelativeGroupLawGrpObj
import Structure.JacJ1Iface
import Abbrev.SheafOfModules_MonoidalV2
import Structure.AlgebraicGeometry_RelSubPicGroup
import Instance.AlgebraicGeometry_RelSubPicGroupV2

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


variable {F N} in


variable {F N}


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


end PresheafOfModules.IsMonoidalW

end

open PresheafOfModules.IsMonoidalW in


end LinkageInlined_68107509

section LinkageInlined_7e0d42f8

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules


end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules in

end LinkageInlined_7e0d42f8

section LinkageInlined_23d4f55a

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits

namespace PresheafOfModules

namespace InvertibleDual

open Opposite InternalHom TensorProduct

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))


private structure TrivializationBelow (X₀ : Cᵒᵖ) where

  gen : ∀ {Y : Cᵒᵖ} (_ : X₀ ⟶ Y), F.obj Y
  compat : ∀ {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z), F.map g (gen f) = gen (f ≫ g)
  bij : ∀ {Y : Cᵒᵖ} (f : X₀ ⟶ Y), Function.Bijective (fun a : R.obj Y => a • gen f)

variable {F} {X₀ : Cᵒᵖ} (D : TrivializationBelow F X₀)

namespace TrivializationBelow


end TrivializationBelow

variable (F) in


end InvertibleDual

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace Opposite PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}


variable (U : X.Opens)


variable {U} (L : X.Modules)


section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)


end


end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in


end LinkageInlined_23d4f55a

end InlinedTheorems

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

end AlgebraicGeometry.RelPicard

end
