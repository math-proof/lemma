module

public import Mathlib
public import Theorem.LinearMap.InternalHom
public import Instance.SheafOfModules_Monoidal
public import Theorem.Scheme.ModulesSectionsTensor
public import Instance.AlgebraicGeometry_ModulesIhomSections
public import Abbrev.AlgebraicGeometry_ModulesIhomSections

public noncomputable section

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


@[simp] public theorem appAt_toPresheafHom (X : Cᵒᵖ) (φ : naturalFamilies F N X) (Y : (Over X.unop)ᵒᵖ)
    (x : F.obj (Opposite.op Y.unop.left)) :
    appAt (toPresheafHom F N X φ) Y x = φ.1 Y.unop.hom.op x := rfl


public theorem ofPresheafHom_app (X : Cᵒᵖ) (s : (linearSub F N).obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) :
    (ofPresheafHom F N X s).1 f x = appAt s.1 (Opposite.op (Over.mk f.unop)) x := rfl


public theorem linearSub_local {J : GrothendieckTopology C}
    (hNsep : Presieve.IsSeparated J (N.presheaf ⋙ forget AddCommGrpCat))
    (X : Cᵒᵖ) (s : (presheafHom F.presheaf N.presheaf).obj X)
    (hs : (linearSub F N).sieveOfSection s ∈ J X.unop) : s ∈ (linearSub F N).obj X := by
  intro Y r x
  obtain ⟨Y⟩ := Y
  apply (hNsep _ (J.pullback_stable Y.hom hs)).ext
  intro W k hk

  have nat : ∀ x' : F.obj (Opposite.op Y.left),
      appAt s (Opposite.op (Over.mk (k ≫ Y.hom))) (F.map k.op x') =
        N.map k.op (appAt s (Opposite.op Y) x') := fun x' =>
    ConcreteCategory.congr_hom (s.naturality (Over.homMk k rfl : Over.mk (k ≫ Y.hom) ⟶ Y).op) x'

  have hlin : ∀ (ρ : R.obj (Opposite.op W)) (z : F.obj (Opposite.op W)),
      appAt s (Opposite.op (Over.mk (k ≫ Y.hom))) (ρ • z) =
        ρ • appAt s (Opposite.op (Over.mk (k ≫ Y.hom))) z := fun ρ z => by
    have h := hk (Opposite.op (Over.mk (𝟙 W))) ρ z
    have e := presheafHom_map_app_op_mk_id (F := F.presheaf) (G := N.presheaf) (k ≫ Y.hom) s
    dsimp only [appAt] at h ⊢
    erw [e] at h
    exact h
  change N.map k.op (appAt s (Opposite.op Y) (r • x)) = N.map k.op (r • appAt s (Opposite.op Y) x)
  rw [← nat, N.map_smul, ← nat, F.map_smul]
  exact hlin _ _

end IsSheafAux

end InternalHom

end PresheafOfModules

end


public theorem PresheafOfModules.ihomObj_isSheaf {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {J : GrothendieckTopology C} (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (PresheafOfModules.ihomObj F N).presheaf := by
  change Presheaf.IsSheaf J (ModuleCat.InternalHom.presheaf F N)
  rw [Presheaf.isSheaf_iff_isSheaf_comp J _ (forget AddCommGrpCat), isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso J (PresheafOfModules.InternalHom.IsSheafAux.isoLinearSub F N).symm ?_
  have hH : Presieve.IsSheaf J (presheafHom F.presheaf N.presheaf) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (hN.hom F.presheaf)
  have hNsep : Presieve.IsSeparated J (N.presheaf ⋙ forget AddCommGrpCat) :=
    ((isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_comp J N.presheaf (forget AddCommGrpCat)).1 hN)).isSeparated
  rw [(PresheafOfModules.InternalHom.IsSheafAux.linearSub F N).isSheaf_iff hH]
  intro X s hs
  exact PresheafOfModules.InternalHom.IsSheafAux.linearSub_local hNsep X s hs

noncomputable section

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}


public theorem ihom_obj_eq_ihomObj (N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (ihom F).obj N = ihomObj F N := rfl


public theorem ihom_map_app_val (ψ : N ⟶ N') {X : Cᵒᵖ} (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : F.obj Y) :
    (((ihom F).map ψ).app X φ).1 f x = ψ.app Y (φ.1 f x) := rfl


public theorem ihom_adjunction_unit_app_val (G : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {X : Cᵒᵖ}
    (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    ((((ihom.adjunction F).unit.app G).app X y) : (ihomObj F (F ⊗ G)).obj X).1 f x =
      x ⊗ₜ[R.obj Y] G.map f y := rfl


public theorem ihom_adjunction_counit_app (N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (ihom.adjunction F).counit.app N = uncurry' F (𝟙 (ihomObj F N)) := rfl

end PresheafOfModules

end

namespace CategoryTheory.MonoidalClosed

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [MonoidalClosed C]


public theorem unitIsoSelf_hom_eq (X : C) :
    (unitIsoSelf X).hom = (λ_ _).inv ≫ (ihom.ev (𝟙_ C)).app X := by
  have h := conjugateEquiv_counit (ihom.adjunction (𝟙_ C)) (Adjunction.id (C := C))
    (leftUnitorNatIso C).inv X
  simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Adjunction.id_counit,
    NatTrans.id_app, Category.comp_id, leftUnitorNatIso_inv_app, ihom.ihom_adjunction_counit] at h
  exact h

end CategoryTheory.MonoidalClosed

noncomputable section

namespace SheafOfModules

open PresheafOfModules ModuleCat.InternalHom Functor.Monoidal Functor.LaxMonoidal ModuleCat
  Functor.OplaxMonoidal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

section unit

variable {𝒪 h𝒪}


public theorem sheafify_map_val_app_unit {P P' : PMod 𝒪} (g : P ⟶ P') (X : Cᵒᵖ) (z : P.obj X) :
    (((sheafifyFunctor 𝒪 h𝒪).map g).val.app X) (((sheafifyAdj 𝒪 h𝒪).unit.app P).app X z) =
      ((sheafifyAdj 𝒪 h𝒪).unit.app P').app X (g.app X z) := by
  have h := (sheafifyAdj 𝒪 h𝒪).unit.naturality g
  exact (congr($(h.symm).app X z) :)


public theorem counit_val_app_unit (N : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) (X : Cᵒᵖ) (y : N.val.obj X) :
    (((sheafifyAdj 𝒪 h𝒪).counit.app N).val.app X)
      (((sheafifyAdj 𝒪 h𝒪).unit.app ((toPMod 𝒪 h𝒪).obj N)).app X y) = y := by
  have h := (sheafifyAdj 𝒪 h𝒪).right_triangle_components N
  exact (congr($(h).app X y) :)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in


public theorem toPMod_obj_map_apply (S : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : S.val.obj X) : ((toPMod 𝒪 h𝒪).obj S).map f x = S.val.map f x := rfl

end unit

variable (M N : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in


public theorem isSheaf_ihomModel : Presheaf.IsSheaf J (ihomModel 𝒪 h𝒪 M N).presheaf :=
  PresheafOfModules.ihomObj_isSheaf _ _ N.isSheaf

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]


public theorem ihom_obj_eq : (ihom M).obj N = (sheafifyFunctor 𝒪 h𝒪).obj (ihomModel 𝒪 h𝒪 M N) := rfl


public theorem ihomSectionsEquivFamily_symm_apply (X : Cᵒᵖ)
    (φ : naturalFamilies ((toPMod 𝒪 h𝒪).obj M) ((toPMod 𝒪 h𝒪).obj N) X) :
    (ihomSectionsEquivFamily 𝒪 h𝒪 M N X).symm φ = (ihomModelToIhom 𝒪 h𝒪 M N).app X φ := rfl


public theorem ihomSectionsEquivFamily_apply (X : Cᵒᵖ) (t : ((ihom M).obj N).val.obj X) :
    ihomSectionsEquivFamily 𝒪 h𝒪 M N X t = (inv (ihomModelToIhom 𝒪 h𝒪 M N)).app X t := rfl


@[simp] public theorem ihomSectionsEquivFamily_unit (X : Cᵒᵖ)
    (φ : naturalFamilies ((toPMod 𝒪 h𝒪).obj M) ((toPMod 𝒪 h𝒪).obj N) X) :
    ihomSectionsEquivFamily 𝒪 h𝒪 M N X ((ihomModelToIhom 𝒪 h𝒪 M N).app X φ) = φ :=
  (ihomSectionsEquivFamily 𝒪 h𝒪 M N X).apply_symm_apply φ


@[simp] public theorem unit_ihomSectionsEquivFamily (X : Cᵒᵖ) (t : ((ihom M).obj N).val.obj X) :
    (ihomModelToIhom 𝒪 h𝒪 M N).app X (ihomSectionsEquivFamily 𝒪 h𝒪 M N X t) = t :=
  (ihomSectionsEquivFamily 𝒪 h𝒪 M N X).symm_apply_apply t


public theorem ihomSectionsEquivFamily_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (t : ((ihom M).obj N).val.obj X) :
    ihomSectionsEquivFamily 𝒪 h𝒪 M N Y (((ihom M).obj N).val.map f t) =
      (ihomModel 𝒪 h𝒪 M N).map f (ihomSectionsEquivFamily 𝒪 h𝒪 M N X t) := by
  apply (ihomSectionsEquivFamily 𝒪 h𝒪 M N Y).symm.injective
  rw [AddEquiv.symm_apply_apply, ihomSectionsEquivFamily_symm_apply, naturality_apply]
  exact congrArg _ (unit_ihomSectionsEquivFamily 𝒪 h𝒪 X t).symm


public theorem ihomSectionsEquivFamily_map_app {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (t : ((ihom M).obj N).val.obj X)
    (g : Y ⟶ Z) (m : M.val.obj Z) :
    (ihomSectionsEquivFamily 𝒪 h𝒪 M N Y (((ihom M).obj N).val.map f t)).1 g m =
      (ihomSectionsEquivFamily 𝒪 h𝒪 M N X t).1 (f ≫ g) m := by
  rw [ihomSectionsEquivFamily_map, ihomObj_map_val]

variable (M N)


public theorem ihomEval_def (X : Cᵒᵖ) (m : M.val.obj X) (t : ((ihom M).obj N).val.obj X) :
    ihomEval 𝒪 h𝒪 M N X m t = (ihomSectionsEquivFamily 𝒪 h𝒪 M N X t).1 (𝟙 X) m := rfl


public theorem ihomSectionsEquivFamily_app_eq_ihomEval {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (t : ((ihom M).obj N).val.obj X) (m : M.val.obj Y) :
    (ihomSectionsEquivFamily 𝒪 h𝒪 M N X t).1 f m =
      ihomEval 𝒪 h𝒪 M N Y m (((ihom M).obj N).val.map f t) := by
  rw [ihomEval_def, ihomSectionsEquivFamily_map_app, Category.comp_id]


@[simp] public theorem ihomEval_unit_app (X : Cᵒᵖ) (m : M.val.obj X)
    (φ : naturalFamilies ((toPMod 𝒪 h𝒪).obj M) ((toPMod 𝒪 h𝒪).obj N) X) :
    ihomEval 𝒪 h𝒪 M N X m ((ihomModelToIhom 𝒪 h𝒪 M N).app X φ) = φ.1 (𝟙 X) m := by
  rw [ihomEval_def, ihomSectionsEquivFamily_unit]


public theorem map_ihomEval {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.val.obj X) (t : ((ihom M).obj N).val.obj X) :
    N.val.map f (ihomEval 𝒪 h𝒪 M N X m t) =
      ihomEval 𝒪 h𝒪 M N Y (M.val.map f m) (((ihom M).obj N).val.map f t) := by
  rw [ihomEval_def, ← ihomSectionsEquivFamily_app_eq_ihomEval]
  exact ((ihomSectionsEquivFamily 𝒪 h𝒪 M N X t).2 (𝟙 X) f m).trans
    (congr_app _ (by simp) _)


public theorem ihom_sections_ext {X : Cᵒᵖ} {t t' : ((ihom M).obj N).val.obj X}
    (h : ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (m : M.val.obj Y),
      ihomEval 𝒪 h𝒪 M N Y m (((ihom M).obj N).val.map f t) =
        ihomEval 𝒪 h𝒪 M N Y m (((ihom M).obj N).val.map f t')) : t = t' := by
  apply (ihomSectionsEquivFamily 𝒪 h𝒪 M N X).injective
  apply naturalFamilies_ext
  intro Y f m
  rw [ihomSectionsEquivFamily_app_eq_ihomEval, ihomSectionsEquivFamily_app_eq_ihomEval]
  exact h f m


public theorem ihomEval_add_right (X : Cᵒᵖ) (m : M.val.obj X) (t t' : ((ihom M).obj N).val.obj X) :
    ihomEval 𝒪 h𝒪 M N X m (t + t') = ihomEval 𝒪 h𝒪 M N X m t + ihomEval 𝒪 h𝒪 M N X m t' := by
  rw [ihomEval_def, map_add]; rfl


public theorem ihomEval_add_left (X : Cᵒᵖ) (m m' : M.val.obj X) (t : ((ihom M).obj N).val.obj X) :
    ihomEval 𝒪 h𝒪 M N X (m + m') t = ihomEval 𝒪 h𝒪 M N X m t + ihomEval 𝒪 h𝒪 M N X m' t :=
  map_add _ _ _


public theorem ihomEval_smul_left (X : Cᵒᵖ) (r : 𝒪.obj X) (m : M.val.obj X)
    (t : ((ihom M).obj N).val.obj X) :
    ihomEval 𝒪 h𝒪 M N X (r • m) t = r • ihomEval 𝒪 h𝒪 M N X m t :=
  ((ihomSectionsEquivFamily 𝒪 h𝒪 M N X t).1 (𝟙 X)).map_smul r m


public theorem ihomEval_smul_right (X : Cᵒᵖ) (r : 𝒪.obj X) (m : M.val.obj X)
    (t : ((ihom M).obj N).val.obj X) :
    ihomEval 𝒪 h𝒪 M N X m (r • t) = r • ihomEval 𝒪 h𝒪 M N X m t := by
  rw [ihomEval_def, ihomEval_def]
  have : ihomSectionsEquivFamily 𝒪 h𝒪 M N X (r • t) = r • ihomSectionsEquivFamily 𝒪 h𝒪 M N X t :=
    (ihomModelSectionsIso 𝒪 h𝒪 M N X).symm.toLinearEquiv.map_smul r t
  rw [this, InternalHom.smul_app]
  erw [𝒪.map_id]
  rfl

variable (M) (P : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))


public theorem sheafifyTensorIso_hom_naturality {M' P' : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)}
    (f : M ⟶ M') (g : P ⟶ P') :
    (sheafifyFunctor 𝒪 h𝒪).map ((toPMod 𝒪 h𝒪).map f ⊗ₘ (toPMod 𝒪 h𝒪).map g) ≫
      (sheafifyTensorIso 𝒪 h𝒪 M' P').hom = (sheafifyTensorIso 𝒪 h𝒪 M P).hom ≫ (f ⊗ₘ g) := by
  dsimp only [sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv, ← Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural, Category.assoc, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
  erw [(sheafifyAdj 𝒪 h𝒪).counit.naturality f, (sheafifyAdj 𝒪 h𝒪).counit.naturality g]
  rfl


public theorem sheafifyTensorNatIso_hom_app :
    (sheafifyTensorNatIso 𝒪 h𝒪 M).hom.app P = (sheafifyTensorIso 𝒪 h𝒪 M P).hom := rfl


public theorem unitIhomNatIso_hom_app : (unitIhomNatIso 𝒪 h𝒪 M).hom.app N = ihomModelToIhom 𝒪 h𝒪 M N := rfl


public theorem ihom_adjunction_eq : ihom.adjunction M =
    (((ihom.adjunction ((toPMod 𝒪 h𝒪).obj M)).comp (sheafifyAdj 𝒪 h𝒪)).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful (toPMod 𝒪 h𝒪)) (Functor.FullyFaithful.id _)
      (sheafifyTensorNatIso 𝒪 h𝒪 M) (unitIhomNatIso 𝒪 h𝒪 M)) := rfl


public theorem tmulSection_def (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X) :
    tmulSection 𝒪 h𝒪 M P X m p = (sheafifyTensorIso 𝒪 h𝒪 M P).hom.val.app X
      (((sheafifyAdj 𝒪 h𝒪).unit.app ((toPMod 𝒪 h𝒪).obj M ⊗ (toPMod 𝒪 h𝒪).obj P)).app X
        (m ⊗ₜ[𝒪.obj X] p)) := rfl


public theorem tensorHom_val_app_tmulSection {M' P' : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)}
    (f : M ⟶ M') (g : P ⟶ P') (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X) :
    (f ⊗ₘ g).val.app X (tmulSection 𝒪 h𝒪 M P X m p) =
      tmulSection 𝒪 h𝒪 M' P' X (f.val.app X m) (g.val.app X p) := by
  have h := congr($(sheafifyTensorIso_hom_naturality 𝒪 h𝒪 f g).val.app X
    (((sheafifyAdj 𝒪 h𝒪).unit.app ((toPMod 𝒪 h𝒪).obj M ⊗ (toPMod 𝒪 h𝒪).obj P)).app X
      (m ⊗ₜ[𝒪.obj X] p)))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h
  rw [tmulSection_def, tmulSection_def, ← h, sheafify_map_val_app_unit]
  rfl


public theorem whiskerLeft_val_app_tmulSection {P' : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)} (g : P ⟶ P')
    (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X) :
    (M ◁ g).val.app X (tmulSection 𝒪 h𝒪 M P X m p) =
      tmulSection 𝒪 h𝒪 M P' X m (g.val.app X p) := by
  rw [← MonoidalCategory.id_tensorHom, tensorHom_val_app_tmulSection]; rfl


public theorem whiskerRight_val_app_tmulSection {M' : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)} (f : M ⟶ M')
    (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X) :
    (f ▷ P).val.app X (tmulSection 𝒪 h𝒪 M P X m p) =
      tmulSection 𝒪 h𝒪 M' P X (f.val.app X m) p := by
  rw [← MonoidalCategory.tensorHom_id, tensorHom_val_app_tmulSection]; rfl


public theorem map_tmulSection {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.val.obj X) (p : P.val.obj X) :
    (M ⊗ P).val.map f (tmulSection 𝒪 h𝒪 M P X m p) =
      tmulSection 𝒪 h𝒪 M P Y (M.val.map f m) (P.val.map f p) := by
  rw [tmulSection_def, tmulSection_def, ← naturality_apply]
  congr 1
  erw [← naturality_apply ((sheafifyAdj 𝒪 h𝒪).unit.app ((toPMod 𝒪 h𝒪).obj M ⊗ (toPMod 𝒪 h𝒪).obj P))
    f (m ⊗ₜ[𝒪.obj X] p)]
  try rfl


public theorem tmulSection_add_left (X : Cᵒᵖ) (m m' : M.val.obj X) (p : P.val.obj X) :
    tmulSection 𝒪 h𝒪 M P X (m + m') p =
      tmulSection 𝒪 h𝒪 M P X m p + tmulSection 𝒪 h𝒪 M P X m' p := by
  rw [tmulSection_def, TensorProduct.add_tmul, map_add, map_add]; rfl


public theorem tmulSection_add_right (X : Cᵒᵖ) (m : M.val.obj X) (p p' : P.val.obj X) :
    tmulSection 𝒪 h𝒪 M P X m (p + p') =
      tmulSection 𝒪 h𝒪 M P X m p + tmulSection 𝒪 h𝒪 M P X m p' := by
  rw [tmulSection_def, TensorProduct.tmul_add, map_add, map_add]; rfl


public theorem tmulSection_smul_left (X : Cᵒᵖ) (r : 𝒪.obj X) (m : M.val.obj X) (p : P.val.obj X) :
    tmulSection 𝒪 h𝒪 M P X (r • m) p = r • tmulSection 𝒪 h𝒪 M P X m p := by
  rw [tmulSection_def, tmulSection_def, ← LinearMap.map_smul]
  erw [← LinearMap.map_smul]
  rw [TensorProduct.smul_tmul']
  rfl


public theorem tmulSection_smul_right (X : Cᵒᵖ) (r : 𝒪.obj X) (m : M.val.obj X) (p : P.val.obj X) :
    tmulSection 𝒪 h𝒪 M P X m (r • p) = r • tmulSection 𝒪 h𝒪 M P X m p := by
  rw [tmulSection_def, tmulSection_def, ← LinearMap.map_smul]
  erw [← LinearMap.map_smul]
  rw [TensorProduct.tmul_smul]
  rfl


public theorem toPMod_map_curry (θ : M ⊗ P ⟶ N) :
    (toPMod 𝒪 h𝒪).map (MonoidalClosed.curry θ) =
      ((ihom.adjunction ((toPMod 𝒪 h𝒪).obj M)).comp (sheafifyAdj 𝒪 h𝒪)).unit.app
          ((toPMod 𝒪 h𝒪).obj P) ≫
        (toPMod 𝒪 h𝒪 ⋙ ihom ((toPMod 𝒪 h𝒪).obj M)).map ((sheafifyTensorNatIso 𝒪 h𝒪 M).hom.app P) ≫
        (toPMod 𝒪 h𝒪 ⋙ ihom ((toPMod 𝒪 h𝒪).obj M)).map ((𝟭 _).map θ) ≫
        (unitIhomNatIso 𝒪 h𝒪 M).hom.app N := by
  have h := Adjunction.restrictFullyFaithful_homEquiv_apply
    ((ihom.adjunction ((toPMod 𝒪 h𝒪).obj M)).comp (sheafifyAdj 𝒪 h𝒪))
    (Functor.FullyFaithful.ofFullyFaithful (toPMod 𝒪 h𝒪)) (Functor.FullyFaithful.id _)
    (sheafifyTensorNatIso 𝒪 h𝒪 M) (unitIhomNatIso 𝒪 h𝒪 M) θ
  have h' := congrArg (toPMod 𝒪 h𝒪).map h
  rw [Functor.FullyFaithful.map_preimage] at h'
  exact h'


public theorem ihomSectionsEquivFamily_curry_app (θ : M ⊗ P ⟶ N) (X : Cᵒᵖ) (p : P.val.obj X) {Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : M.val.obj Y) :
    (ihomSectionsEquivFamily 𝒪 h𝒪 M N X ((MonoidalClosed.curry θ).val.app X p)).1 f x =
      θ.val.app Y (tmulSection 𝒪 h𝒪 M P Y x (P.val.map f p)) := by
  have h := congr($(toPMod_map_curry 𝒪 h𝒪 θ).app X p)
  change (ihomSectionsEquivFamily 𝒪 h𝒪 M N X
    (((toPMod 𝒪 h𝒪).map (MonoidalClosed.curry θ)).app X p)).1 f x = _
  rw [h]
  simp only [Functor.comp_map, Functor.id_map, Adjunction.comp_unit_app, unitIhomNatIso_hom_app,
    sheafifyTensorNatIso_hom_app, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  erw [ihomSectionsEquivFamily_unit]
  rfl


public theorem ihomEval_curry (θ : M ⊗ P ⟶ N) (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X) :
    ihomEval 𝒪 h𝒪 M N X m ((MonoidalClosed.curry θ).val.app X p) =
      θ.val.app X (tmulSection 𝒪 h𝒪 M P X m p) := by
  rw [ihomEval_def, ihomSectionsEquivFamily_curry_app]
  erw [ModuleCat.InternalHom.map_id_apply]


public theorem ihom_ev_val_app_tmulSection (X : Cᵒᵖ) (m : M.val.obj X) (t : ((ihom M).obj N).val.obj X) :
    ((ihom.ev M).app N).val.app X (tmulSection 𝒪 h𝒪 M ((ihom M).obj N) X m t) =
      ihomEval 𝒪 h𝒪 M N X m t := by
  have h := ihomEval_curry 𝒪 h𝒪 (N := N) ((ihom.ev M).app N) X m t
  rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry,
    MonoidalClosed.uncurry_id_eq_ev] at h
  exact h.symm


public theorem uncurry_val_app_tmulSection (κ : P ⟶ (ihom M).obj N) (X : Cᵒᵖ) (m : M.val.obj X)
    (p : P.val.obj X) :
    (MonoidalClosed.uncurry κ).val.app X (tmulSection 𝒪 h𝒪 M P X m p) =
      ihomEval 𝒪 h𝒪 M N X m (κ.val.app X p) := by
  rw [MonoidalClosed.uncurry_eq, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, whiskerLeft_val_app_tmulSection]
  exact ihom_ev_val_app_tmulSection 𝒪 h𝒪 X m _


public theorem ihom_hom_ext {κ κ' : P ⟶ (ihom M).obj N}
    (h : ∀ (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X),
      ihomEval 𝒪 h𝒪 M N X m (κ.val.app X p) = ihomEval 𝒪 h𝒪 M N X m (κ'.val.app X p)) :
    κ = κ' := by
  ext X p
  apply ihom_sections_ext 𝒪 h𝒪
  intro Y f m
  rw [← naturality_apply, ← naturality_apply]
  exact h Y m _


public theorem tensor_hom_ext {θ θ' : M ⊗ P ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X),
      θ.val.app X (tmulSection 𝒪 h𝒪 M P X m p) = θ'.val.app X (tmulSection 𝒪 h𝒪 M P X m p)) :
    θ = θ' := by
  apply MonoidalClosed.curry_injective
  apply ihom_hom_ext 𝒪 h𝒪
  intro X m p
  rw [ihomEval_curry, ihomEval_curry, h]


public theorem ihomEval_ihom_map_val_app {N' : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)} (g : N ⟶ N')
    (X : Cᵒᵖ) (m : M.val.obj X) (t : ((ihom M).obj N).val.obj X) :
    ihomEval 𝒪 h𝒪 M N' X m (((ihom M).map g).val.app X t) =
      g.val.app X (ihomEval 𝒪 h𝒪 M N X m t) := by
  have h : (ihom M).map g = MonoidalClosed.curry ((ihom.ev M).app N ≫ g) := by
    rw [← MonoidalClosed.curry_uncurry ((ihom M).map g), MonoidalClosed.uncurry_ihom_map]
  rw [h, ihomEval_curry, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  exact congrArg _ (ihom_ev_val_app_tmulSection 𝒪 h𝒪 X m t)


public theorem ihomEval_pre_val_app {A B : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)} (f : B ⟶ A) (X : Cᵒᵖ)
    (b : B.val.obj X) (t : ((ihom A).obj N).val.obj X) :
    ihomEval 𝒪 h𝒪 B N X b (((MonoidalClosed.pre f).app N).val.app X t) =
      ihomEval 𝒪 h𝒪 A N X (f.val.app X b) t := by
  have h : (MonoidalClosed.pre f).app N =
      MonoidalClosed.curry (f ▷ _ ≫ (ihom.ev A).app N) := by
    rw [← MonoidalClosed.curry_uncurry ((MonoidalClosed.pre f).app N), MonoidalClosed.uncurry_pre]
  rw [h, ihomEval_curry, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, whiskerRight_val_app_tmulSection]
  exact ihom_ev_val_app_tmulSection 𝒪 h𝒪 X _ t


public theorem ε_sheafifyFunctor :
    Functor.LaxMonoidal.ε (sheafifyFunctor 𝒪 h𝒪) = (sheafifyUnitIso 𝒪 h𝒪).inv := rfl


public theorem sheafifyUnitIso_hom_eq_counit :
    (sheafifyUnitIso 𝒪 h𝒪).hom = (sheafifyAdj 𝒪 h𝒪).counit.app (𝟙_ _) := rfl

set_option maxHeartbeats 400000 in
variable (P) in


public theorem sheafifyTensorIso_hom_leftUnitor_hom :
    (sheafifyTensorIso 𝒪 h𝒪 (𝟙_ _) P).hom ≫ (λ_ P).hom =
      (sheafifyFunctor 𝒪 h𝒪).map (λ_ ((toPMod 𝒪 h𝒪).obj P)).hom ≫
        (sheafifyAdj 𝒪 h𝒪).counit.app P := by
  dsimp only [sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.id_obj]
  rw [Functor.Monoidal.μIso_inv, MonoidalCategory.tensorHom_def, Category.assoc, Category.assoc,
    MonoidalCategory.leftUnitor_naturality]
  erw [Functor.LaxMonoidal.left_unitality (sheafifyFunctor 𝒪 h𝒪) ((toPMod 𝒪 h𝒪).obj P)]
  simp only [Functor.comp_obj, Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ε_sheafifyFunctor,
    ← sheafifyUnitIso_hom_eq_counit, Iso.hom_inv_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp]
  erw [Functor.Monoidal.δ_μ_assoc]

set_option maxHeartbeats 800000 in


public theorem leftUnitor_hom_val_app_tmulSection (X : Cᵒᵖ) (r : 𝒪.obj X) (p : P.val.obj X) :
    (λ_ P).hom.val.app X (tmulSection 𝒪 h𝒪 (𝟙_ _) P X r p) = r • p := by
  have h := congr($(sheafifyTensorIso_hom_leftUnitor_hom 𝒪 h𝒪 P).val.app X
    (((sheafifyAdj 𝒪 h𝒪).unit.app ((toPMod 𝒪 h𝒪).obj (𝟙_ _) ⊗ (toPMod 𝒪 h𝒪).obj P)).app X
      (r ⊗ₜ[𝒪.obj X] p)))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h
  rw [tmulSection_def, h]
  erw [sheafify_map_val_app_unit, counit_val_app_unit]
  exact TensorProduct.lid_tmul p r

set_option maxHeartbeats 400000 in


public theorem leftUnitor_inv_val_app (X : Cᵒᵖ) (p : P.val.obj X) :
    (λ_ P).inv.val.app X p = tmulSection 𝒪 h𝒪 (𝟙_ _) P X (1 : 𝒪.obj X) p := by
  have hli : Function.LeftInverse ((λ_ P).inv.val.app X) ((λ_ P).hom.val.app X) := fun a => by
    have h := congr($((λ_ P).hom_inv_id).val.app X a)
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h
    exact h
  apply hli.injective
  rw [leftUnitor_hom_val_app_tmulSection, one_smul]
  have h := congr($((λ_ P).inv_hom_id).val.app X p)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h
  exact h

set_option maxHeartbeats 400000 in


public theorem unitIsoSelf_hom_val_app (X : Cᵒᵖ) (t : ((ihom (𝟙_ _)).obj N).val.obj X) :
    (MonoidalClosed.unitIsoSelf N).hom.val.app X t = ihomEval 𝒪 h𝒪 (𝟙_ _) N X (1 : 𝒪.obj X) t := by
  rw [CategoryTheory.MonoidalClosed.unitIsoSelf_hom_eq, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply, leftUnitor_inv_val_app]
  exact ihom_ev_val_app_tmulSection 𝒪 h𝒪 X _ t

end SheafOfModules

end

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}}


public theorem toPMod_obj_map_apply (S : X.Modules) {V V' : (X.Opens)ᵒᵖ} (f : V ⟶ V') (x : S.val.obj V) :
    ((toPMod X).obj S).map f x = S.val.map f x := rfl

section restrict

set_option maxHeartbeats 400000

variable (U : X.Opens)

variable {U} in

public theorem image_preimage_eq_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h


public theorem restrict_ringHom_apply (W : (U : Scheme.{u}).Opens) (a : Γ(X, U.ι ''ᵁ W)) :
    (U.ι.appIso W).inv.hom a = a := by
  rw [Scheme.Opens.ι_appIso]; rfl

variable (M N : X.Modules)

variable {U M} in


public theorem restrict_smul_eq (W : (U : Scheme.{u}).Opens) (a : Γ(↑U, W)) (y : Γ(M.restrict U.ι, W)) :
    (a • y : Γ(M.restrict U.ι, W)) =
      ((show Γ(X, U.ι ''ᵁ W) from a) • (show Γ(M, U.ι ''ᵁ W) from y) : Γ(M, U.ι ''ᵁ W)) :=
  (show (a • y : Γ(M.restrict U.ι, W)) =
      ((U.ι.appIso W).inv.hom a • (show Γ(M, U.ι ''ᵁ W) from y) : Γ(M, U.ι ''ᵁ W)) from rfl).trans
    (by rw [restrict_ringHom_apply])

set_option maxHeartbeats 800000 in


@[simp] public theorem restrictHomOfFamily_app_apply
    (φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op U))
    (W : (U : Scheme.{u}).Opens) (x : Γ(M, U.ι ''ᵁ W)) :
    (restrictHomOfFamily U M N φ).app W x = φ.1 (opHomImage U W) x := rfl

variable {U M N} in


public theorem restrictHomAppLE_apply (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {V : X.Opens} (h : V ≤ U)
    (x : Γ(M, V)) :
    restrictHomAppLE ψ h x = N.presheaf.map (eqToHom (image_preimage_eq_of_le h).symm).op
      (ψ.app (U.ι ⁻¹ᵁ V) (M.presheaf.map (eqToHom (image_preimage_eq_of_le h)).op x)) := rfl


public theorem map_restrictHomAppLE (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {V V' : X.Opens} (h : V ≤ U)
    (i : V' ⟶ V) (x : Γ(M, V)) :
    N.presheaf.map i.op (restrictHomAppLE ψ h x) =
      restrictHomAppLE ψ (i.le.trans h) (M.presheaf.map i.op x) := by
  rw [restrictHomAppLE_apply, restrictHomAppLE_apply]
  have hle : U.ι ⁻¹ᵁ V' ≤ U.ι ⁻¹ᵁ V := fun p hp => i.le hp
  have nat := congr($(ψ.mapPresheaf.naturality (homOfLE hle).op)
    (M.presheaf.map (eqToHom (image_preimage_eq_of_le h)).op x))
  simp only [ConcreteCategory.comp_apply, Modules.mapPresheaf_app, Opposite.unop_op,
    Modules.restrict_map] at nat
  have eM : M.presheaf.map (U.ι.opensFunctor.map (homOfLE hle)).op
      (M.presheaf.map (eqToHom (image_preimage_eq_of_le h)).op x) =
      M.presheaf.map (eqToHom (image_preimage_eq_of_le (i.le.trans h))).op
        (M.presheaf.map i.op x) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    exact congrArg (fun k => M.presheaf.map k x) (Subsingleton.elim _ _)
  have eN : ∀ z, N.presheaf.map i.op
      (N.presheaf.map (eqToHom (image_preimage_eq_of_le h).symm).op z) =
      N.presheaf.map (eqToHom (image_preimage_eq_of_le (i.le.trans h)).symm).op
        (N.presheaf.map (U.ι.opensFunctor.map (homOfLE hle)).op z) := fun z => by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    exact congrArg (fun k => N.presheaf.map k z) (Subsingleton.elim _ _)
  rw [eN, ← eM]
  exact congrArg (fun z => N.presheaf.map
    (eqToHom (image_preimage_eq_of_le (i.le.trans h)).symm).op z) nat.symm


public theorem restrictHomAppLE_image (ψ : M.restrict U.ι ⟶ N.restrict U.ι) (W : (U : Scheme.{u}).Opens)
    (x : Γ(M, U.ι ''ᵁ W)) :
    restrictHomAppLE ψ (U.ι_image_le W) x = ψ.app W x := by
  rw [restrictHomAppLE_apply]
  have hle : W ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ W) := (U.ι.preimage_image_eq W).ge
  have nat := congr($(ψ.mapPresheaf.naturality (homOfLE hle).op)
    (M.presheaf.map (eqToHom (image_preimage_eq_of_le (U.ι_image_le W))).op x))
  simp only [ConcreteCategory.comp_apply, Modules.mapPresheaf_app, Opposite.unop_op,
    Modules.restrict_map] at nat
  have eM : M.presheaf.map (U.ι.opensFunctor.map (homOfLE hle)).op
      (M.presheaf.map (eqToHom (image_preimage_eq_of_le (U.ι_image_le W))).op x) = x := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact (congrArg (fun k => M.presheaf.map k x) (Subsingleton.elim _ (𝟙 _))).trans
      (by rw [CategoryTheory.Functor.map_id]; rfl)
  have e1 : N.presheaf.map (eqToHom (image_preimage_eq_of_le (U.ι_image_le W)).symm).op
      (ψ.app (U.ι ⁻¹ᵁ (U.ι ''ᵁ W))
        (M.presheaf.map (eqToHom (image_preimage_eq_of_le (U.ι_image_le W))).op x)) =
      N.presheaf.map (U.ι.opensFunctor.map (homOfLE hle)).op
      (ψ.app (U.ι ⁻¹ᵁ (U.ι ''ᵁ W))
        (M.presheaf.map (eqToHom (image_preimage_eq_of_le (U.ι_image_le W))).op x)) :=
    congrArg (fun k => N.presheaf.map k _) (Subsingleton.elim _ _)
  rw [e1]
  exact nat.symm.trans (congrArg (fun z => ψ.app W z) eM)

variable (U M N)


public theorem familyOfRestrictHom_app (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {V : (X.Opens)ᵒᵖ}
    (f : Opposite.op U ⟶ V) (x : Γ(M, V.unop)) :
    (familyOfRestrictHom U M N ψ).1 f x = restrictHomAppLE ψ (V := V.unop) f.unop.le x := rfl


@[simp] public theorem restrictHomEquivFamily_apply (ψ : M.restrict U.ι ⟶ N.restrict U.ι) :
    restrictHomEquivFamily U M N ψ = familyOfRestrictHom U M N ψ := rfl


@[simp] public theorem restrictHomEquivFamily_symm_apply
    (φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op U)) :
    (restrictHomEquivFamily U M N).symm φ = restrictHomOfFamily U M N φ := rfl

end restrict

variable (M N : X.Modules)


public theorem tmulSection_eq_tensorSections {U : X.Opens} (m : Γ(M, U)) (p : Γ(P, U)) :
    SheafOfModules.tmulSection X.sheaf.obj X.ringCatSheaf.property M P (Opposite.op U) m p =
      tensorSections m p := rfl


public theorem map_ihomEval {U V : X.Opens} (i : V ⟶ U) (m : Γ(M, U)) (t : Γ((ihom M).obj N, U)) :
    N.presheaf.map i.op (ihomEval M N U m t) =
      ihomEval M N V (M.presheaf.map i.op m) (((ihom M).obj N).presheaf.map i.op t) :=
  SheafOfModules.map_ihomEval _ _ i.op m t


public theorem ihom_sections_ext {U : X.Opens} {t t' : Γ((ihom M).obj N, U)}
    (h : ∀ ⦃V : X.Opens⦄ (i : V ⟶ U) (m : Γ(M, V)),
      ihomEval M N V m (((ihom M).obj N).presheaf.map i.op t) =
        ihomEval M N V m (((ihom M).obj N).presheaf.map i.op t')) : t = t' :=
  SheafOfModules.ihom_sections_ext _ _ (fun _ f m => h f.unop m)


public theorem ihomEval_add_left (U : X.Opens) (m m' : Γ(M, U)) (t : Γ((ihom M).obj N, U)) :
    ihomEval M N U (m + m') t = ihomEval M N U m t + ihomEval M N U m' t :=
  SheafOfModules.ihomEval_add_left _ _ _ m m' t


public theorem ihomEval_add_right (U : X.Opens) (m : Γ(M, U)) (t t' : Γ((ihom M).obj N, U)) :
    ihomEval M N U m (t + t') = ihomEval M N U m t + ihomEval M N U m t' :=
  SheafOfModules.ihomEval_add_right _ _ _ m t t'


public theorem ihomEval_smul_left (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) (t : Γ((ihom M).obj N, U)) :
    ihomEval M N U (r • m) t = r • ihomEval M N U m t :=
  SheafOfModules.ihomEval_smul_left _ _ _ r m t


public theorem ihomEval_smul_right (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) (t : Γ((ihom M).obj N, U)) :
    ihomEval M N U m (r • t) = r • ihomEval M N U m t :=
  SheafOfModules.ihomEval_smul_right _ _ _ r m t


@[simp] public theorem ihomEval_zero_left (U : X.Opens) (t : Γ((ihom M).obj N, U)) :
    ihomEval M N U 0 t = 0 := map_zero _


@[simp] public theorem ihomEval_zero_right (U : X.Opens) (m : Γ(M, U)) :
    ihomEval M N U m 0 = 0 := by
  have h := ihomEval_add_right (M := M) (N := N) U m 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h


public theorem ihomEval_curry_app (θ : M ⊗ P ⟶ N) (U : X.Opens) (m : Γ(M, U)) (p : Γ(P, U)) :
    ihomEval M N U m ((MonoidalClosed.curry θ).app U p) = θ.app U (tensorSections m p) := by
  rw [← tmulSection_eq_tensorSections]
  exact SheafOfModules.ihomEval_curry _ _ θ _ m p


public theorem ihom_ev_app_tensorSections (U : X.Opens) (m : Γ(M, U)) (t : Γ((ihom M).obj N, U)) :
    ((ihom.ev M).app N).app U (tensorSections m t) = ihomEval M N U m t := by
  rw [← tmulSection_eq_tensorSections]
  exact SheafOfModules.ihom_ev_val_app_tmulSection _ _ _ m t


public theorem uncurry_app_tensorSections (κ : P ⟶ (ihom M).obj N) (U : X.Opens) (m : Γ(M, U))
    (p : Γ(P, U)) :
    (MonoidalClosed.uncurry κ).app U (tensorSections m p) = ihomEval M N U m (κ.app U p) := by
  rw [← tmulSection_eq_tensorSections]
  exact SheafOfModules.uncurry_val_app_tmulSection _ _ κ _ m p


public theorem ihom_hom_ext {κ κ' : P ⟶ (ihom M).obj N}
    (h : ∀ (U : X.Opens) (m : Γ(M, U)) (p : Γ(P, U)),
      ihomEval M N U m (κ.app U p) = ihomEval M N U m (κ'.app U p)) : κ = κ' :=
  SheafOfModules.ihom_hom_ext _ _ (fun U m p => h U.unop m p)


public theorem tensor_hom_ext {θ θ' : M ⊗ P ⟶ N}
    (h : ∀ (U : X.Opens) (m : Γ(M, U)) (p : Γ(P, U)),
      θ.app U (tensorSections m p) = θ'.app U (tensorSections m p)) : θ = θ' :=
  SheafOfModules.tensor_hom_ext X.sheaf.obj X.ringCatSheaf.property (fun ⟨U⟩ m p => by
    rw [tmulSection_eq_tensorSections]; exact h U m p)


public theorem ihomEval_ihom_map_app {N' : X.Modules} (g : N ⟶ N') (U : X.Opens) (m : Γ(M, U))
    (t : Γ((ihom M).obj N, U)) :
    ihomEval M N' U m (((ihom M).map g).app U t) = g.app U (ihomEval M N U m t) :=
  SheafOfModules.ihomEval_ihom_map_val_app _ _ g _ m t


public theorem ihomEval_pre_app {A B : X.Modules} (f : B ⟶ A) (U : X.Opens) (b : Γ(B, U))
    (t : Γ((ihom A).obj N, U)) :
    ihomEval B N U b (((MonoidalClosed.pre f).app N).app U t) = ihomEval A N U (f.app U b) t :=
  SheafOfModules.ihomEval_pre_val_app _ _ f _ b t

variable (N) in


public theorem unitIsoSelf_hom_app (U : X.Opens) (t : Γ((ihom (𝟙_ X.Modules)).obj N, U)) :
    (MonoidalClosed.unitIsoSelf N).hom.app U t = ihomEval (𝟙_ X.Modules) N U (unitSection U) t :=
  SheafOfModules.unitIsoSelf_hom_val_app _ _ _ t

variable (M N)


public theorem ihomSectionsEquiv_apply (U : X.Opens) (t : Γ((ihom M).obj N, U)) :
    ihomSectionsEquiv M N U t = restrictHomOfFamily U M N
      (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property M N
        (Opposite.op U) t) := rfl


public theorem ihomSectionsEquiv_symm_apply (U : X.Opens) (ψ : M.restrict U.ι ⟶ N.restrict U.ι) :
    (ihomSectionsEquiv M N U).symm ψ =
      (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property M N
        (Opposite.op U)).symm (familyOfRestrictHom U M N ψ) := rfl


public theorem ihomSectionsEquiv_app_apply (U : X.Opens) (t : Γ((ihom M).obj N, U))
    (W : (U : Scheme.{u}).Opens) (m : Γ(M, U.ι ''ᵁ W)) :
    (ihomSectionsEquiv M N U t).app W m =
      ihomEval M N (U.ι ''ᵁ W) m (((ihom M).obj N).presheaf.map (homOfLE (U.ι_image_le W)).op t) := by
  rw [ihomSectionsEquiv_apply, restrictHomOfFamily_app_apply,
    SheafOfModules.ihomSectionsEquivFamily_app_eq_ihomEval]
  rfl


public theorem ihomEval_map_ihomSectionsEquiv_symm {U V : X.Opens} (h : V ≤ U)
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) (m : Γ(M, V)) :
    ihomEval M N V m (((ihom M).obj N).presheaf.map (homOfLE h).op ((ihomSectionsEquiv M N U).symm ψ)) =
      N.presheaf.map (eqToHom (image_preimage_eq_of_le h).symm).op
        (ψ.app (U.ι ⁻¹ᵁ V) (M.presheaf.map (eqToHom (image_preimage_eq_of_le h)).op m)) := by
  change SheafOfModules.ihomEval X.sheaf.obj X.ringCatSheaf.property M N (Opposite.op V) m
    (((ihom M).obj N).val.map (homOfLE h).op
      ((SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property M N
        (Opposite.op U)).symm (familyOfRestrictHom U M N ψ))) = _
  erw [← SheafOfModules.ihomSectionsEquivFamily_app_eq_ihomEval X.sheaf.obj X.ringCatSheaf.property
    (M := M) (N := N) (homOfLE h).op]
  rw [AddEquiv.apply_symm_apply]
  rfl


public theorem ihomEval_map_ihomSectionsEquiv_symm_image (U : X.Opens)
    (ψ : M.restrict U.ι ⟶ N.restrict U.ι) (W : (U : Scheme.{u}).Opens) (m : Γ(M, U.ι ''ᵁ W)) :
    ihomEval M N (U.ι ''ᵁ W) m
      (((ihom M).obj N).presheaf.map (homOfLE (U.ι_image_le W)).op
        ((ihomSectionsEquiv M N U).symm ψ)) = ψ.app W m := by
  rw [← ihomSectionsEquiv_app_apply, AddEquiv.apply_symm_apply]


public theorem ihomEval_eqToHom {A B : X.Opens} (e : A = B) (m : Γ(M, A)) (t : Γ((ihom M).obj N, A)) :
    ihomEval M N B (M.presheaf.map (eqToHom e.symm).op m)
      (((ihom M).obj N).presheaf.map (eqToHom e.symm).op t) =
      N.presheaf.map (eqToHom e.symm).op (ihomEval M N A m t) := by
  subst e
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl


public theorem ihomSectionsEquiv_map_app_apply {U V : X.Opens} (h : V ≤ U) (t : Γ((ihom M).obj N, U))
    (W : (V : Scheme.{u}).Opens) (W' : (U : Scheme.{u}).Opens) (e : U.ι ''ᵁ W' = V.ι ''ᵁ W)
    (m : Γ(M, U.ι ''ᵁ W')) :
    (ihomSectionsEquiv M N V (((ihom M).obj N).presheaf.map (homOfLE h).op t)).app W
        (M.presheaf.map (eqToHom e.symm).op m) =
      N.presheaf.map (eqToHom e.symm).op ((ihomSectionsEquiv M N U t).app W' m) := by
  rw [ihomSectionsEquiv_app_apply, ihomSectionsEquiv_app_apply, ← ihomEval_eqToHom e]
  congr 1
  change (((ihom M).obj N).presheaf.map _ ≫ ((ihom M).obj N).presheaf.map _) t =
    (((ihom M).obj N).presheaf.map _ ≫ ((ihom M).obj N).presheaf.map _) t
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

variable (M N)


@[simp] public theorem homOfFamily_app_apply
    (φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op ⊤))
    (V : X.Opens) (x : Γ(M, V)) : (homOfFamily M N φ).app V x = φ.1 (homOfLE le_top).op x := rfl


@[simp] public theorem familyOfHom_app (ψ : M ⟶ N) {V : (X.Opens)ᵒᵖ} (f : Opposite.op ⊤ ⟶ V)
    (x : Γ(M, V.unop)) : (familyOfHom M N ψ).1 f x = ψ.app V.unop x := rfl


public theorem ihomGlobalSectionsEquiv_app_apply (t : Γ((ihom M).obj N, ⊤)) (V : X.Opens) (m : Γ(M, V)) :
    (ihomGlobalSectionsEquiv M N t).app V m =
      ihomEval M N V m (((ihom M).obj N).presheaf.map (homOfLE le_top).op t) := by
  change ((SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property M N
    (Opposite.op ⊤)) t).1 (homOfLE le_top).op m = _
  rw [SheafOfModules.ihomSectionsEquivFamily_app_eq_ihomEval]
  rfl


public theorem ihomEval_map_ihomGlobalSectionsEquiv_symm (ψ : M ⟶ N) (V : X.Opens) (m : Γ(M, V)) :
    ihomEval M N V m
      (((ihom M).obj N).presheaf.map (homOfLE le_top).op ((ihomGlobalSectionsEquiv M N).symm ψ)) =
      ψ.app V m := by
  rw [← ihomGlobalSectionsEquiv_app_apply, AddEquiv.apply_symm_apply]


public theorem ihomEval_ihomGlobalSectionsEquiv_symm (ψ : M ⟶ N) (m : Γ(M, ⊤)) :
    ihomEval M N ⊤ m ((ihomGlobalSectionsEquiv M N).symm ψ) = ψ.app ⊤ m := by
  rw [← ihomEval_map_ihomGlobalSectionsEquiv_symm ψ ⊤ m]
  congr 1
  change _ = (((ihom M).obj N).presheaf.map (𝟙 _)) _
  rw [CategoryTheory.Functor.map_id]
  rfl


public theorem ihomSectionsEquiv_map_app_apply_of_top (t : Γ((ihom M).obj N, ⊤)) (U : X.Opens)
    (W : (U : Scheme.{u}).Opens) (m : Γ(M, U.ι ''ᵁ W)) :
    (ihomSectionsEquiv M N U (((ihom M).obj N).presheaf.map (homOfLE le_top).op t)).app W m =
      (ihomGlobalSectionsEquiv M N t).app (U.ι ''ᵁ W) m := by
  rw [ihomSectionsEquiv_app_apply, ihomGlobalSectionsEquiv_app_apply]
  congr 1
  change (((ihom M).obj N).presheaf.map _ ≫ ((ihom M).obj N).presheaf.map _) t = _
  rw [← Functor.map_comp]
  rfl

section restrictUnit

variable {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]


@[simp] public theorem restrictUnitIso_hom_app_apply (U : X.Opens) (r : Γ((𝟙_ Y.Modules).restrict f, U)) :
    (restrictUnitIso' f).hom.app U r = (f.appIso U).hom.hom r := rfl


@[simp] public theorem restrictUnitIso_inv_app_apply (U : X.Opens) (r : Γ(𝟙_ X.Modules, U)) :
    (restrictUnitIso' f).inv.app U r = (f.appIso U).inv.hom r := rfl


public theorem restrictUnitIso_ι_hom_app_apply (U : X.Opens) (W : (U : Scheme.{u}).Opens)
    (r : Γ((𝟙_ X.Modules).restrict U.ι, W)) :
    (restrictUnitIso' U.ι).hom.app W r = (show Γ(X, U.ι ''ᵁ W) from r) := by
  rw [restrictUnitIso_hom_app_apply, Scheme.Opens.ι_appIso]; rfl

end restrictUnit

end AlgebraicGeometry.Scheme.Modules

end
