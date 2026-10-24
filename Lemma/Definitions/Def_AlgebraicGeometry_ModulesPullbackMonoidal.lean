import Mathlib
import Lemma.Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Lemma.Definitions.Def_SheafOfModules_Monoidal
import Lemma.Definitions.Def_PresheafOfModules_PullbackMonoidal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance preservesBinaryProducts_opensMap :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have hinf : K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩ ≤ c.pt := leOfHom (hc.lift
          { pt := K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩
            π := Discrete.natTrans (fun j => match j with
              | ⟨.left⟩ => homOfLE inf_le_left
              | ⟨.right⟩ => homOfLE inf_le_right) })
        have h₁ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.left⟩) := leOfHom (s.π.app ⟨.left⟩)
        have h₂ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.right⟩) := leOfHom (s.π.app ⟨.right⟩)
        exact (le_inf h₁ h₂).trans (leOfHom ((Opens.map f.base).map (homOfLE hinf))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesTerminal_opensMap :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have htop : (⊤ : Y.Opens) ≤ c.pt := leOfHom (hc.lift
          { pt := ⊤, π := Discrete.natTrans (fun j => j.as.elim) })
        exact le_top.trans (leOfHom ((Opens.map f.base).map (homOfLE htop))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesFiniteProducts_opensMap : PreservesFiniteProducts (Opens.map f.base) :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

abbrev pullback₀ : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

instance pullback₀_monoidal : (pullback₀ f).Monoidal :=
  inferInstanceAs (PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).Monoidal

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

variable (Y) in
instance sheafify_isLocalization' : (Modules.sheafify Y).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
  inferInstanceAs ((SheafOfModules.sheafifyFunctor Y.sheaf.obj Y.ringCatSheaf.property).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj))

instance : Localization.Lifting (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩

instance pullback_monoidal : (Modules.pullback f).Monoidal :=
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  Localization.Monoidal.functorMonoidalOfComp (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)

def pullbackTensorObjIso (L M : Y.Modules) :
    (Modules.pullback f).obj (L ⊗ M) ≅ (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj M :=
  (Functor.Monoidal.μIso (Modules.pullback f) L M).symm

def pullbackTensorUnitObjIso : (Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (Functor.Monoidal.εIso (Modules.pullback f)).symm

end AlgebraicGeometry.Scheme.Modules

end
