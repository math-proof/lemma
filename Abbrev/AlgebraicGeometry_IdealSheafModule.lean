import Instance.SheafOfModules_Monoidal
import Structure.AlgebraicGeometry_RelEffCartierDiv
import Lemma.AlgebraicGeometry.RelEffCartierDiv

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

namespace Scheme.IdealSheafData

def module (I : X.IdealSheafData) : X.Modules :=
  (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)

def moduleι (I : X.IdealSheafData) : I.module ⟶ 𝟙_ X.Modules :=
  kernel.ι I.subschemeι.unitToPushforwardUnit

def invModule (I : X.IdealSheafData) : X.Modules :=
  Scheme.Modules.dual I.module

end Scheme.IdealSheafData

abbrev RelEffCartierDiv.idealModule {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.module

abbrev RelEffCartierDiv.lineBundle {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.invModule

end AlgebraicGeometry

end
