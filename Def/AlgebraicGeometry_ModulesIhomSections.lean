module
public import Mathlib
public import Def.AlgebraicGeometry_InternalHom
public import Instance.SheafOfModules_Monoidal
public import Def.AlgebraicGeometry_ModulesSectionsTensor
public import Instance.AlgebraicGeometry_ModulesIhomSections
public import Abbrev.AlgebraicGeometry_ModulesIhomSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


public section

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace PresheafOfModules

namespace InternalHom

namespace IsSheafAux

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

noncomputable def toPresheafHom (X : Cᵒᵖ) (φ : naturalFamilies F N X) :
    (presheafHom F.presheaf N.presheaf).obj X where
  app Y := AddCommGrpCat.ofHom (φ.1 Y.unop.hom.op).toAddMonoidHom
  naturality {Y Y'} k := by
    ext x
    change φ.1 Y'.unop.hom.op (F.map k.unop.left.op x) = N.map k.unop.left.op (φ.1 Y.unop.hom.op x)
    rw [φ.2 Y.unop.hom.op k.unop.left.op x]
    exact congr_app φ (by rw [← op_comp, Over.w]) _

noncomputable def linearSub : Subfunctor (presheafHom F.presheaf N.presheaf) where
  obj X := { s | ∀ (Y : (Over X.unop)ᵒᵖ) (r : R.obj (Opposite.op Y.unop.left))
    (x : F.obj (Opposite.op Y.unop.left)), appAt s Y (r • x) = r • appAt s Y x }
  map h _ hs Y r x := hs (Opposite.op ((Over.map h.unop).obj Y.unop)) r x

noncomputable def ofPresheafHom (X : Cᵒᵖ) (s : (linearSub F N).obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => appAt s.1 (Opposite.op (Over.mk f.unop)) x
      map_add' := fun x x' => (s.1.app _).hom.map_add _ _
      map_smul' := fun r x => s.2 (Opposite.op (Over.mk f.unop)) r x }, by
    intro Y Z f g x
    change N.map g (appAt s.1 (Opposite.op (Over.mk f.unop)) x) =
      appAt s.1 (Opposite.op (Over.mk (g.unop ≫ f.unop))) (F.map g x)
    have := s.1.naturality (Over.homMk g.unop rfl : Over.mk (g.unop ≫ f.unop) ⟶ Over.mk f.unop).op
    exact (ConcreteCategory.congr_hom this x).symm⟩

noncomputable def equivLinearSub (X : Cᵒᵖ) : naturalFamilies F N X ≃ (linearSub F N).obj X where
  toFun φ := ⟨toPresheafHom F N X φ, fun Y r x => (φ.1 Y.unop.hom.op).map_smul r x⟩
  invFun s := ofPresheafHom F N X s
  left_inv φ := by
    apply naturalFamilies_ext; intro Y f x; rfl
  right_inv s := by rfl

noncomputable def isoLinearSub :
    InternalHom.presheaf F N ⋙ forget AddCommGrpCat ≅ (linearSub F N).toFunctor :=
  NatIso.ofComponents (fun X => (equivLinearSub F N X).toIso) (by intros; rfl)

variable {F N}

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


noncomputable section

namespace SheafOfModules

open PresheafOfModules ModuleCat.InternalHom Functor.Monoidal Functor.LaxMonoidal ModuleCat
  Functor.OplaxMonoidal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]


variable (M N : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

def ihomModelToIhom : ihomModel 𝒪 h𝒪 M N ⟶ (toPMod 𝒪 h𝒪).obj ((ihom M).obj N) :=
  (sheafifyAdj 𝒪 h𝒪).unit.app (ihomModel 𝒪 h𝒪 M N)

def ihomModelSectionsIso (X : Cᵒᵖ) :
    (ihomModel 𝒪 h𝒪 M N).obj X ≅ ((toPMod 𝒪 h𝒪).obj ((ihom M).obj N)).obj X :=
  (PresheafOfModules.evaluation _ X).mapIso (asIso (ihomModelToIhom 𝒪 h𝒪 M N))

def ihomSectionsEquivFamily (X : Cᵒᵖ) :
    ((ihom M).obj N).val.obj X ≃+ naturalFamilies ((toPMod 𝒪 h𝒪).obj M) ((toPMod 𝒪 h𝒪).obj N) X :=
  ((ihomModelSectionsIso 𝒪 h𝒪 M N X).toLinearEquiv.toAddEquiv).symm

variable {M N}

variable (M N)

def ihomEval (X : Cᵒᵖ) (m : M.val.obj X) (t : ((ihom M).obj N).val.obj X) : N.val.obj X :=
  (ihomSectionsEquivFamily 𝒪 h𝒪 M N X t).1 (𝟙 X) m

variable {M N}

variable (M) (P : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪))

def sheafifyTensorIso : (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M ⊗ (toPMod 𝒪 h𝒪).obj P) ≅
    M ⊗ P :=
  (μIso (sheafifyFunctor 𝒪 h𝒪) _ _).symm ≪≫
    asIso (((sheafifyAdj 𝒪 h𝒪).counit.app M) ⊗ₘ ((sheafifyAdj 𝒪 h𝒪).counit.app P))

variable {M P} in
def sheafifyTensorNatIso :
    toPMod 𝒪 h𝒪 ⋙ (tensorLeft ((toPMod 𝒪 h𝒪).obj M) ⋙ sheafifyFunctor 𝒪 h𝒪) ≅ tensorLeft M ⋙ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ (μIso (sheafifyFunctor 𝒪 h𝒪) _ _).symm ≪≫
      asIso (((sheafifyAdj 𝒪 h𝒪).counit.app _) ⊗ₘ ((sheafifyAdj 𝒪 h𝒪).counit.app _)))
    (fun {P P'} g ↦ by
      have h := sheafifyTensorIso_hom_naturality 𝒪 h𝒪 (𝟙 M) g
      rw [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom,
        MonoidalCategory.id_tensorHom] at h
      exact h)

def unitIhomNatIso : 𝟭 _ ⋙ (toPMod 𝒪 h𝒪 ⋙ ihom ((toPMod 𝒪 h𝒪).obj M)) ≅
    (toPMod 𝒪 h𝒪 ⋙ ihom ((toPMod 𝒪 h𝒪).obj M) ⋙ sheafifyFunctor 𝒪 h𝒪) ⋙ toPMod 𝒪 h𝒪 :=
  NatIso.ofComponents (fun _ ↦ asIso ((sheafifyAdj 𝒪 h𝒪).unit.app ((ihom _).obj _)))
    (fun _ ↦ (sheafifyAdj 𝒪 h𝒪).unit.naturality _)

def tmulSection (X : Cᵒᵖ) (m : M.val.obj X) (p : P.val.obj X) : (M ⊗ P).val.obj X :=
  (sheafifyTensorIso 𝒪 h𝒪 M P).hom.val.app X
    (((sheafifyAdj 𝒪 h𝒪).unit.app ((toPMod 𝒪 h𝒪).obj M ⊗ (toPMod 𝒪 h𝒪).obj P)).app X
      (m ⊗ₜ[𝒪.obj X] p))

variable {M P}


end SheafOfModules

end

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}}

section restrict

set_option maxHeartbeats 400000

variable (U : X.Opens)

variable (M N : X.Modules)

variable {U M} in

set_option maxHeartbeats 800000 in

def restrictHomOfFamily
    (φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op U)) :
    M.restrict U.ι ⟶ N.restrict U.ι :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (φ.1 (opHomImage U W.unop)).toAddMonoidHom
      naturality := fun {W W'} i => by
        ext x
        change φ.1 (opHomImage U W'.unop) (M.val.map (U.ι.opensFunctor.map i.unop).op x) =
          N.val.map (U.ι.opensFunctor.map i.unop).op (φ.1 (opHomImage U W.unop) x)
        erw [φ.2 (opHomImage U W.unop) (U.ι.opensFunctor.map i.unop).op x]
        exact ModuleCat.InternalHom.congr_app φ (Subsingleton.elim _ _) _ }
    (fun W a x =>

      (congrArg (φ.1 (opHomImage U W.unop)) (restrict_smul_eq (M := M) W.unop a x)).trans
        (((φ.1 (opHomImage U W.unop)).map_smul _ _).trans
          (restrict_smul_eq (M := N) W.unop a (φ.1 (opHomImage U W.unop) x)).symm))⟩

variable {U M N} in

def restrictHomAppLE (ψ : M.restrict U.ι ⟶ N.restrict U.ι) {V : X.Opens} (h : V ≤ U) :
    Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) where
  toFun x := N.presheaf.map (eqToHom (image_preimage_eq_of_le h).symm).op
    (ψ.app (U.ι ⁻¹ᵁ V) (M.presheaf.map (eqToHom (image_preimage_eq_of_le h)).op x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    rw [RingHom.id_apply, Modules.map_smul, ← restrict_smul_eq, Modules.Hom.app_smul,
      restrict_smul_eq, Modules.map_smul]
    congr 1
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]

variable {U M N}

variable (U M N)

def familyOfRestrictHom (ψ : M.restrict U.ι ⟶ N.restrict U.ι) :
    PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op U) :=
  ⟨fun V f => restrictHomAppLE ψ (V := V.unop) (f.unop.le : V.unop ≤ U),
    fun V V' f g x => map_restrictHomAppLE ψ (V := V.unop) (V' := V'.unop) f.unop.le g.unop x⟩

def restrictHomEquivFamily :
    (M.restrict U.ι ⟶ N.restrict U.ι) ≃+
      PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
        (Opposite.op U) where
  toFun := familyOfRestrictHom U M N
  invFun := restrictHomOfFamily U M N
  left_inv ψ := by
    ext W x
    exact restrictHomAppLE_image ψ W x
  right_inv φ := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro V f x
    have h1 := φ.2 (opHomImage U (U.ι ⁻¹ᵁ V.unop))
      (eqToHom (image_preimage_eq_of_le (f.unop.le : V.unop ≤ U)).symm).op
      (((toPMod X).obj M).map (eqToHom (image_preimage_eq_of_le (f.unop.le : V.unop ≤ U))).op x)
    have h2 : ((toPMod X).obj M).map
        (eqToHom (image_preimage_eq_of_le (f.unop.le : V.unop ≤ U)).symm).op
        (((toPMod X).obj M).map
          (eqToHom (image_preimage_eq_of_le (f.unop.le : V.unop ≤ U))).op x) = x := by
      erw [← PresheafOfModules.map_comp_apply]
      rw [((toPMod X).obj M).congr_map_apply (Subsingleton.elim _ (𝟙 _))]
      exact ModuleCat.InternalHom.map_id_apply _ _ _
    exact (h1.trans (congrArg (fun z => φ.1 (opHomImage U (U.ι ⁻¹ᵁ V.unop) ≫
      (eqToHom (image_preimage_eq_of_le (f.unop.le : V.unop ≤ U)).symm).op) z) h2)).trans
      (ModuleCat.InternalHom.congr_app φ (Subsingleton.elim _ _) _)
  map_add' ψ ψ' := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro V f x
    change restrictHomAppLE (ψ + ψ') (V := V.unop) f.unop.le x =
      restrictHomAppLE ψ (V := V.unop) f.unop.le x + restrictHomAppLE ψ' (V := V.unop) f.unop.le x
    rw [restrictHomAppLE_apply, restrictHomAppLE_apply, restrictHomAppLE_apply, Modules.Hom.add_app,
      AddCommGrpCat.hom_add_apply, map_add]

end restrict

variable (M N : X.Modules)

def ihomEval (U : X.Opens) (m : Γ(M, U)) (t : Γ((ihom M).obj N, U)) : Γ(N, U) :=
  SheafOfModules.ihomEval X.sheaf.obj X.ringCatSheaf.property M N (Opposite.op U) m t

variable {M N} {P : X.Modules}


variable (M N)

def ihomSectionsEquiv (U : X.Opens) :
    Γ((ihom M).obj N, U) ≃+ (M.restrict U.ι ⟶ N.restrict U.ι) :=
  (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property M N
    (Opposite.op U)).trans (restrictHomEquivFamily U M N).symm

variable {M N}

variable (M N)

def homOfFamily (φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op ⊤)) :
    M ⟶ N :=
  ⟨{ app := fun V => ModuleCat.ofHom
        { toFun := fun x => φ.1 (homOfLE le_top).op x
          map_add' := fun x y => (φ.1 _).map_add x y
          map_smul' := fun r x => (φ.1 (homOfLE le_top).op).map_smul r x }
     naturality := fun {V V'} i => by
       ext x
       change φ.1 (homOfLE le_top).op (M.val.map i x) = N.val.map i (φ.1 (homOfLE le_top).op x)
       erw [φ.2 (homOfLE le_top).op i x]
       exact ModuleCat.InternalHom.congr_app φ (Subsingleton.elim _ _) _ }⟩

def familyOfHom (ψ : M ⟶ N) :
    PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M) ((toPMod X).obj N)
      (Opposite.op ⊤) :=
  ⟨fun V _ =>
    { toFun := fun x => ψ.val.app V x
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r x => (ψ.val.app V).hom.map_smul r x },
    fun _ _ _ g x => (PresheafOfModules.naturality_apply ψ.val g x).symm⟩

def homEquivFamily :
    (M ⟶ N) ≃+ PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj M)
      ((toPMod X).obj N) (Opposite.op ⊤) where
  toFun := familyOfHom M N
  invFun := homOfFamily M N
  left_inv ψ := by ext V x; rfl
  right_inv φ := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro V f x
    exact ModuleCat.InternalHom.congr_app φ (Subsingleton.elim _ _) _
  map_add' ψ ψ' := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro V f x
    rfl

def ihomGlobalSectionsEquiv : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N) :=
  (SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property M N
    (Opposite.op ⊤)).trans (homEquivFamily M N).symm

variable {M N}

section restrictUnit

variable {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

def restrictUnitIso' : (𝟙_ Y.Modules).restrict f ≅ 𝟙_ X.Modules where
  hom := ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (f.appIso U.unop).hom.hom.toAddMonoidHom
      naturality := fun {U V} i => by
        ext x
        have nat := congr($(f.appIso_inv_naturality (U := U.unop) (V := V.unop) i).hom
          ((f.appIso U.unop).hom.hom x))
        have hx : (f.appIso U.unop).inv.hom ((f.appIso U.unop).hom.hom x) = x := by
          have h := congr($((f.appIso U.unop).hom_inv_id).hom x)
          simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
            RingHom.id_apply] at h
          exact h
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, hx] at nat
        refine (show _ = (f.appIso V.unop).hom.hom
          ((Y.presheaf.map (f.opensFunctor.op.map i)).hom x) from rfl).trans ?_
        refine (congrArg (fun z => (f.appIso V.unop).hom.hom z) nat.symm).trans ?_
        have h := congr($((f.appIso V.unop).inv_hom_id).hom
          ((X.presheaf.map i).hom ((f.appIso U.unop).hom.hom x)))
        simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
          RingHom.id_apply] at h
        exact h }
    (fun U a x => by
      refine (show _ = (f.appIso U.unop).hom.hom
        ((f.appIso U.unop).inv.hom a * (show Γ(Y, f ''ᵁ U.unop) from x)) from rfl).trans ?_
      rw [map_mul]
      have h := congr($((f.appIso U.unop).inv_hom_id).hom a)
      simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
        RingHom.id_apply] at h
      rw [h]
      rfl)⟩
  inv := ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (f.appIso U.unop).inv.hom.toAddMonoidHom
      naturality := fun {U V} i => by
        ext y
        have nat := congr($(f.appIso_inv_naturality (U := U.unop) (V := V.unop) i).hom y)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat
        exact (show _ = (f.appIso V.unop).inv.hom ((X.presheaf.map i).hom y) from rfl).trans nat }
    (fun U a y => by
      refine (show _ = (f.appIso U.unop).inv.hom
        ((show Γ(X, U.unop) from a) * (show Γ(X, U.unop) from y)) from rfl).trans ?_
      rw [map_mul]
      rfl)⟩
  hom_inv_id := by
    ext U x
    refine (show _ = (f.appIso U).inv.hom ((f.appIso U).hom.hom x) from rfl).trans ?_
    have h := congr($((f.appIso U).hom_inv_id).hom x)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at h
    exact h
  inv_hom_id := by
    ext U y
    refine (show _ = (f.appIso U).hom.hom ((f.appIso U).inv.hom y) from rfl).trans ?_
    have h := congr($((f.appIso U).inv_hom_id).hom y)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at h
    exact h

end restrictUnit

end AlgebraicGeometry.Scheme.Modules

end
