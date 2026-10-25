import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u v₁ u₁ v₂ u₂

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

section restrictScalars

variable {C : Type u₁} [Category.{v₁} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)

abbrev ringCatHom : S ⋙ forget₂ CommRingCat RingCat ⟶ R ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

noncomputable abbrev restrictScalarsAt (U : Cᵒᵖ) : ModuleCat.{u} (R.obj U) ⥤ ModuleCat.{u} (S.obj U) :=
  ModuleCat.restrictScalars (φ.app U).hom

end restrictScalars

section pushforward


end pushforward

end PresheafOfModules

namespace CategoryTheory.Limits

end CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

local notation "R'" => R ⋙ forget₂ CommRingCat RingCat

end PresheafOfModules

namespace PresheafOfModules

namespace PullbackMonoidal

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasFiniteProducts C] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteProducts F]
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

local notation "R'" => R ⋙ forget₂ CommRingCat RingCat
local notation "S'" => S ⋙ forget₂ CommRingCat RingCat

noncomputable abbrev pf : PresheafOfModules.{u} R' ⥤ PresheafOfModules.{u} S' :=
  pushforward (R := R') (ringCatHom φ)

noncomputable abbrev pb : PresheafOfModules.{u} S' ⥤ PresheafOfModules.{u} R' :=
  pullback (R := R') (ringCatHom φ)

noncomputable abbrev adj : pb F φ ⊣ pf F φ := pullbackPushforwardAdjunction (R := R') (ringCatHom φ)

noncomputable abbrev gS (U : C) : PresheafOfModules.{u} S' := (free S').obj (yoneda.obj U)
noncomputable abbrev gR (V : D) : PresheafOfModules.{u} R' := (free R').obj (yoneda.obj V)

noncomputable abbrev h₂ (U : C) :
    (pf F φ ⋙ coyoneda.obj (op (gS U))).CorepresentableBy (gR (F.obj U)) :=
  pushforwardCompCoyonedaFreeYonedaCorepresentableBy (R := R') (ringCatHom φ) U

end PullbackMonoidal

end PresheafOfModules
