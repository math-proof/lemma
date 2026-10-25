import Mathlib
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Instance.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open NeronModelInfra

noncomputable section

namespace AlgebraicGeometry

structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

def Scheme.Modules.pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  sorry

theorem Scheme.Modules.isInvertible_unit (X : Scheme.{u}) :
    Scheme.Modules.IsInvertible (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩⟩

theorem Scheme.Modules.IsInvertible.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback f).obj L) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hyU, ⟨eU⟩⟩ := hL.1 (f.base x)
  refine ⟨f ⁻¹ᵁ U, hyU, ⟨?_⟩⟩
  have hfact : (f ⁻¹ᵁ U).ι ≫ f = (f ∣_ U) ≫ U.ι := (morphismRestrict_ι f U).symm
  exact
    (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfact).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso eU ≪≫
    Scheme.Modules.pullbackUnitIso (f ∣_ U)

namespace RelPicard

variable {R : Type u} [CommRing R]


def rigSection {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    T ⟶ pullback c t :=
  pullback.lift (t ≫ ε.1) (𝟙 T) (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])


structure RigidifiedLineBundle {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : Type (u + 1) where

  L : (pullback c t).Modules
  isInvertible : Scheme.Modules.IsInvertible L
  rigidified : Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj L ≅
    SheafOfModules.unit T.ringCatSheaf)

namespace RigidifiedLineBundle

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

def unit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : RigidifiedLineBundle c ε t where
  L := SheafOfModules.unit (pullback c t).ringCatSheaf
  isInvertible := Scheme.Modules.isInvertible_unit _
  rigidified := ⟨Scheme.Modules.pullbackUnitIso _⟩


end RigidifiedLineBundle


end RelPicard

end AlgebraicGeometry

end
