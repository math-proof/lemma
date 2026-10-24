import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open NeronModelInfra

noncomputable section

namespace AlgebraicGeometry

structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

instance Scheme.Hom.opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

def Scheme.Modules.pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  haveI h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  exact @asIso _ _ _ _ _ h

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

def baseChangeSnd {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (s : SchemeHomOver t' t) : pullback c t' ⟶ pullback c t :=
  pullback.map c t' c t (𝟙 C) s.1 (𝟙 _)
    ((Category.comp_id c).trans (Category.id_comp c).symm) ((Category.comp_id t').trans s.2.symm)

def rigSection {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    T ⟶ pullback c t :=
  pullback.lift (t ≫ ε.1) (𝟙 T) (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])

def postComp {X X' T' : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)}
    {x' : X' ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver x x') (ψ : SchemeHomOver t' x) : SchemeHomOver t' x' :=
  ⟨ψ.1 ≫ φ.1, by rw [Category.assoc, φ.2, ψ.2]⟩

theorem baseChangeSnd_id {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) :
    baseChangeSnd c (⟨𝟙 T, Category.id_comp t⟩ : SchemeHomOver t t) = 𝟙 (pullback c t) :=
  pullback.map_id

theorem baseChangeSnd_comp {C X X' T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {x : X ⟶ Spec (CommRingCat.of R)} {x' : X' ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver x x') (ψ : SchemeHomOver t' x) :
    baseChangeSnd c ψ ≫ baseChangeSnd c φ = baseChangeSnd c (postComp φ ψ) := by
  unfold baseChangeSnd postComp
  refine (pullback.map_comp (𝟙 C) (𝟙 C) ψ.1 φ.1
    (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R))) _ _ _ _).trans ?_
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, Category.comp_id]

theorem rigSection_baseChangeSnd {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (g : SchemeHomOver t' t) :
    rigSection c t' ε ≫ baseChangeSnd c g = g.1 ≫ rigSection c t ε := by
  unfold rigSection baseChangeSnd
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
    rw [← Category.assoc, g.2]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.comp_id, Category.id_comp]

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

instance {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Inhabited (RigidifiedLineBundle c ε t) := ⟨unit t⟩

def pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (ψ : SchemeHomOver t' t) : RigidifiedLineBundle c ε t' where
  L := (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ)).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    (Scheme.Modules.pullback ψ.1).mapIso M.rigidified.some ≪≫
    Scheme.Modules.pullbackUnitIso ψ.1⟩

instance setoid {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Setoid (RigidifiedLineBundle c ε t) where
  r M M' := Nonempty (M.L ≅ M'.L)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i ≪≫ j⟩⟩

theorem pullbackAlong_congr {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {M M' : RigidifiedLineBundle c ε t}
    (ψ : SchemeHomOver t' t) (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((M.pullbackAlong ψ).L ≅ (M'.pullbackAlong ψ).L) :=
  ⟨(Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso h.some⟩

def Classes (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : Type (u + 1) :=
  Quotient (RigidifiedLineBundle.setoid (c := c) (ε := ε) t)

def classesMap {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Classes c ε t → Classes c ε t' :=
  Quotient.map (fun M => M.pullbackAlong ψ) (fun _ _ h => pullbackAlong_congr ψ h)

end RigidifiedLineBundle

def relPicardPresheaf {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) where
  obj X := RigidifiedLineBundle.Classes c ε X.unop.hom
  map {X X'} φ := TypeCat.ofHom
    (RigidifiedLineBundle.classesMap (c := c) (ε := ε)
      (⟨φ.unop.left, Over.w φ.unop⟩ : SchemeHomOver X'.unop.hom X.unop.hom))
  map_id X := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ M =>
      exact Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c X.unop.hom)).app M.L ≪≫
          (Scheme.Modules.pullbackId (pullback c X.unop.hom)).app M.L⟩)
  map_comp {X X' X''} φ χ := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ M =>
      exact Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr
            (baseChangeSnd_comp c
              (⟨φ.unop.left, Over.w φ.unop⟩ : SchemeHomOver X'.unop.hom X.unop.hom)
              (⟨χ.unop.left, Over.w χ.unop⟩ :
                SchemeHomOver X''.unop.hom X'.unop.hom)).symm).app M.L ≪≫
          ((Scheme.Modules.pullbackComp _ _).app M.L).symm⟩)

def relPicardPresheaf.unitClass {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (X : Over (Spec (CommRingCat.of R))) :
    (relPicardPresheaf c ε).obj (Opposite.op X) :=
  Quotient.mk _ (RigidifiedLineBundle.unit X.hom)

end RelPicard

end AlgebraicGeometry

end
