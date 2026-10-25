import Abbrev.AlgebraicGeometry_IdealSheafModule
import Abbrev.AlgebraicGeometry_IdealSheafModuleMaps

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData)

open Opposite

@[reassoc]
lemma comapSubschemeHom_comp :
    I.comapSubschemeHom f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  simp [comapSubschemeHom]

lemma kernelι_unitToPushforwardUnit_map_eq_zero :
    (kernel.ι I.subschemeι.unitToPushforwardUnit ≫ f.unitToPushforwardUnit) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map
        (I.comap f).subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m

  set s : Γ(X, U.unop) := (kernel.ι I.subschemeι.unitToPushforwardUnit).val.app U m with hs_def
  have hs : I.subschemeι.app U.unop s = 0 := by
    have := congrArg (fun φ ↦ φ.val.app U m) (kernel.condition I.subschemeι.unitToPushforwardUnit)
    exact this

  have hs' : (I.subschemeι.app U.unop).hom s = 0 := hs

  have h0 : ((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s = 0 := by
    change ((I.comapSubschemeHom f).app _).hom ((I.subschemeι.app U.unop).hom s) = 0
    rw [hs', map_zero]

  have key := congrArg (fun φ ↦ φ.hom s)
    (Scheme.Hom.congr_app (I.comapSubschemeHom_comp f).symm U.unop)
  change (((I.comap f).subschemeι ≫ f).app U.unop).hom s = 0
  rw [key]
  change ((I.comap f).subscheme.presheaf.map _).hom
    (((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s) = 0
  rw [h0, map_zero]

def moduleToPushforwardComapModule :
    (I.module : SheafOfModules X.ringCatSheaf) ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (I.comap f).module :=
  kernel.lift _ _ (I.kernelι_unitToPushforwardUnit_map_eq_zero f) ≫
    (PreservesKernel.iso (SheafOfModules.pushforward f.toRingCatSheafHom)
      (I.comap f).subschemeι.unitToPushforwardUnit).inv

def pullbackModuleComparison :
    (Scheme.Modules.pullback f).obj I.module ⟶ (I.comap f).module :=
  ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _).symm
    (I.moduleToPushforwardComapModule f)

end AlgebraicGeometry.Scheme.IdealSheafData

end
