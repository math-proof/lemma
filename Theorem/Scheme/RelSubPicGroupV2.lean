module

public import Mathlib
public import Def.AlgebraicGeometry_RelativePicardFunctor
public import Theorem.Scheme.RepresentsRelSubPic
public import Def.AlgebraicGeometry_RelSubPicPresheaf
public import Theorem.Scheme.RelativeGroupLawGrpObj
public import Structure.JacJ1Iface
public import Abbrev.SheafOfModules_MonoidalV2
public import Theorem.Scheme.RelSubPicGroup
public import Instance.AlgebraicGeometry_RelSubPicGroupV2
public import Structure.AlgebraicGeometry_RelSubPicGroupV2

public noncomputable section

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


@[local simp] public theorem appAt_toPresheafHom (X : Cᵒᵖ) (φ : naturalFamilies F N X) (Y : (Over X.unop)ᵒᵖ)
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

end InternalHom

end PresheafOfModules

end


public theorem PresheafOfModules.isSheaf_ihomObj_loc {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {J : GrothendieckTopology C} (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (PresheafOfModules.ihomObj F N).presheaf := by
  change Presheaf.IsSheaf J (ModuleCat.InternalHom.presheaf F N)
  rw [Presheaf.isSheaf_iff_isSheaf_comp J _ (forget AddCommGrpCat), isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso J (PresheafOfModules.InternalHom.isoLinearSub F N).symm ?_
  have hH : Presieve.IsSheaf J (presheafHom F.presheaf N.presheaf) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (hN.hom F.presheaf)
  have hNsep : Presieve.IsSeparated J (N.presheaf ⋙ forget AddCommGrpCat) :=
    ((isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_comp J N.presheaf (forget AddCommGrpCat)).1 hN)).isSeparated
  rw [(PresheafOfModules.InternalHom.linearSub F N).isSheaf_iff hH]
  intro X s hs
  exact PresheafOfModules.InternalHom.linearSub_local hNsep X s hs

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


public theorem W_eq : W (J := J) 𝒪 = (MorphismProperty.isomorphisms _).inverseImage (shf 𝒪 R α) :=
  PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α


public theorem isIso_unit_app_of_isSheaf (N : PMod 𝒪) (hN : Presheaf.IsSheaf J N.presheaf) :
    IsIso ((adj 𝒪 R α).unit.app N) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map ((adj 𝒪 R α).unit.app N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J hN
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)


public theorem isIso_shf_map_unit_whiskerRight (d d' : PMod 𝒪) :
    IsIso ((shf 𝒪 R α).map (((adj 𝒪 R α).unit.app d) ▷ d')) := by
  have h := (Monoidal.Reflective.isIso_tfae (adj 𝒪 R α)).out 0 2
  refine (h.mp ?_) d d'
  intro c d
  apply isIso_unit_app_of_isSheaf
  exact PresheafOfModules.isSheaf_ihomObj_loc _ _ c.isSheaf

include R α in

public theorem W_whiskerRight {d₁ d₂ : PMod 𝒪} (g : d₁ ⟶ d₂) (hg : W (J := J) 𝒪 g) (d' : PMod 𝒪) :
    W (J := J) 𝒪 (g ▷ d') := by
  have two3 : (W (J := J) 𝒪).HasTwoOutOfThreeProperty := by
    rw [W_eq 𝒪 R α]; infer_instance
  have hη : ∀ d : PMod 𝒪, W (J := J) 𝒪 ((adj 𝒪 R α).unit.app d ▷ d') := fun d => by
    rw [W_eq 𝒪 R α]
    exact isIso_shf_map_unit_whiskerRight 𝒪 R α d d'
  have hiso : W (J := J) 𝒪 ((inc 𝒪 R α).map ((shf 𝒪 R α).map g) ▷ d') := by
    rw [W_eq 𝒪 R α] at hg ⊢
    simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at hg ⊢
    have : IsIso ((inc 𝒪 R α).map ((shf 𝒪 R α).map g)) := Functor.map_isIso _ _
    infer_instance
  have e := (adj 𝒪 R α).unit_naturality g
  have hη₁ := hη d₁
  have hη₂ := hη d₂

  dsimp only [Functor.comp_obj, Functor.id_obj] at e hη₁ hη₂ hiso ⊢
  have h' := (W (J := J) 𝒪).comp_mem _ _ hη₁ hiso
  rw [← comp_whiskerRight, e, comp_whiskerRight] at h'
  exact (W (J := J) 𝒪).of_postcomp _ _ hη₂ h'

end PresheafOfModules.IsMonoidalW

end

open PresheafOfModules.IsMonoidalW in


public theorem PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf_loc {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
    (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerRight g hg d' := W_whiskerRight 𝒪 R α g hg d'
  whiskerLeft d g₁ g₂ g hg :=
    ((W (J := J) 𝒪).arrow_mk_iso_iff (Arrow.isoMk' (g ▷ d) (d ◁ g) (β_ g₁ d) (β_ g₂ d)
      (BraidedCategory.braiding_naturality_left g d).symm)).1 (W_whiskerRight 𝒪 R α g hg d)

end LinkageInlined_68107509

section LinkageInlined_7e0d42f8

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme.Modules


public theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_loc {X : AlgebraicGeometry.Scheme.{u}}
    {L M : X.Modules} (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (L ⊗ M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  obtain ⟨U', hxU', ⟨eU'⟩⟩ := hM.1 x
  refine ⟨U ⊓ U', ⟨hxU, hxU'⟩, ⟨?_⟩⟩
  exact pullbackTensorObjIso (U ⊓ U').ι L M ≪≫
    (trivializationOfLE inf_le_left L eU ⊗ᵢ trivializationOfLE inf_le_right M eU') ≪≫
    λ_ (𝟙_ _)

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


public theorem coord_smul_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) : D.coord f x • D.gen f = x :=
  (D.triv f).apply_symm_apply x


public theorem coord_gen_smul {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (a : R.obj Y) : D.coord f (a • D.gen f) = a :=
  (D.triv f).symm_apply_apply a


@[local simp] public theorem coord_gen {Y : Cᵒᵖ} (f : X₀ ⟶ Y) : D.coord f (D.gen f) = 1 := by
  simpa using D.coord_gen_smul f 1


public theorem coord_map {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y) :
    D.coord (f ≫ g) (F.map g x) = R.map g (D.coord f x) := by
  conv_lhs => rw [← D.coord_smul_gen f x]
  rw [PresheafOfModules.map_smul, D.compat]
  exact D.coord_gen_smul (f ≫ g) _


@[local simp] public theorem dualGen_app {Y : Cᵒᵖ} (f : X₀ ⟶ Y) (x : F.obj Y) :
    (D.dualGen).1 f x = D.coord f x := rfl


public theorem eq_smul_dualGen (φ : (dual F).obj X₀) : φ = φ.1 (𝟙 X₀) (D.gen (𝟙 X₀)) • D.dualGen := by
  apply naturalFamilies_ext
  intro Y f x
  rw [InternalHom.smul_app, dualGen_app]
  conv_lhs => rw [← D.coord_smul_gen f x, LinearMap.map_smul]
  have h := InternalHom.naturality φ (𝟙 X₀) f (D.gen (𝟙 X₀))
  rw [D.compat, Category.id_comp] at h
  rw [← h, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl


public theorem ev_app_tmul (x : F.obj X₀) (φ : (dual F).obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (x ⊗ₜ[R.obj X₀] φ) = φ.1 (𝟙 X₀) x :=
  uncurry'_app_tmul F (𝟙 (dual F)) x φ


public theorem ev_evInv (a : R.obj X₀) :
    DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (D.evInv a) = a := by
  change DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ => (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
      ((ev F).app X₀).hom (a • (D.gen (𝟙 X₀) ⊗ₜ[R.obj X₀] D.dualGen)) = a
  rw [LinearMap.map_smul]
  erw [ev_app_tmul]
  rw [dualGen_app, coord_gen, smul_eq_mul, mul_one]


public theorem evInv_ev (z : (F.obj X₀ ⊗[R.obj X₀] (dual F).obj X₀)) :
    D.evInv (DFunLike.coe (α := (F.obj X₀ ⊗ (dual F).obj X₀ :)) (β := fun _ =>
      (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))).obj X₀)
        ((ev F).app X₀).hom z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul x φ =>
    erw [ev_app_tmul]
    set d : R.obj X₀ := φ.1 (𝟙 X₀) (D.gen (𝟙 X₀)) with hd
    have hx : x = D.coord (𝟙 X₀) x • D.gen (𝟙 X₀) := (D.coord_smul_gen _ x).symm
    have hφ : φ = d • D.dualGen := D.eq_smul_dualGen φ
    have h1 : φ.1 (𝟙 X₀) x = D.coord (𝟙 X₀) x * d := by
      conv_lhs => rw [hx]
      rw [LinearMap.map_smul, smul_eq_mul]
    rw [h1]
    conv_rhs => rw [hx, hφ, TensorProduct.smul_tmul_smul]
    rfl


public theorem ev_app_bijective (D : TrivializationBelow F X₀) : Function.Bijective ((ev F).app X₀) :=
  Function.bijective_iff_has_inverse.2 ⟨D.evInv, D.evInv_ev, D.ev_evInv⟩

end TrivializationBelow

variable (F) in


public theorem W_ev {J : GrothendieckTopology C} [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hloc : ∀ (U : C), ∃ (S : Sieve U), S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f → Nonempty (TrivializationBelow F (op V))) :
    J.W ((toPresheaf _).map (ev F)) := by
  have hsurj : Presheaf.IsLocallySurjective J ((toPresheaf _).map (ev F)) := by
    constructor
    intro U s
    obtain ⟨S, hS, hS'⟩ := hloc U
    refine J.superset_covering ?_ hS
    intro V i hi
    obtain ⟨D⟩ := hS' i hi
    obtain ⟨t, ht⟩ := D.ev_app_bijective.2 (((𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat))).presheaf.map i.op) s)
    exact ⟨t, ht⟩
  have hinj : Presheaf.IsLocallyInjective J ((toPresheaf _).map (ev F)) := by
    constructor
    intro U x y h
    obtain ⟨S, hS, hS'⟩ := hloc U.unop
    refine J.superset_covering ?_ hS
    intro V i hi
    obtain ⟨D⟩ := hS' i hi
    have nx := ConcreteCategory.congr_hom (((toPresheaf _).map (ev F)).naturality i.op) x
    have ny := ConcreteCategory.congr_hom (((toPresheaf _).map (ev F)).naturality i.op) y
    simp only [ConcreteCategory.comp_apply] at nx ny
    change (F ⊗ dual F).presheaf.map i.op x = (F ⊗ dual F).presheaf.map i.op y
    apply D.ev_app_bijective.1
    change ((toPresheaf _).map (ev F)).app _ ((F ⊗ dual F).presheaf.map i.op x) =
      ((toPresheaf _).map (ev F)).app _ ((F ⊗ dual F).presheaf.map i.op y)
    erw [nx, ny, h]
  exact J.W_of_isLocallyBijective _

end InvertibleDual

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace Opposite PresheafOfModules.InvertibleDual

variable {X : Scheme.{u}}


public theorem restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl


public theorem image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)


public theorem gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • gen₀ L e W := by
  have := (e.inv.val.app (op W)).hom.map_smul b (1 : Γ(U, W))
  rw [smul_eq_mul, mul_one] at this
  exact this


public theorem gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective (fun b : Γ(X, U.ι ''ᵁ W) => b • gen₀ L e W) := by
  have h : Function.Bijective ((e.inv.val.app (op W)).hom) := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.hom.val.app (op W)).hom, fun b => ?_, fun m => ?_⟩
    · exact congr($(e.inv_hom_id).val.app (op W) |>.hom b)
    · exact congr($(e.hom_inv_id).val.app (op W) |>.hom m)
  exact (funext (gen₀_spec L e W) ▸ h :)


public theorem gen₀_map {W W' : (U : Scheme.{u}).Opens} (i : W' ⟶ W) :
    L.val.map (U.ι.opensFunctor.map i).op (gen₀ L e W) = gen₀ L e W' := by
  have := PresheafOfModules.naturality_apply e.inv.val i.op (1 : Γ(U, W))

  rw [show ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.map i.op) (1 : Γ(U, W)) =
    (1 : Γ(U, W')) from ((U : Scheme.{u}).presheaf.map i.op).hom.map_one] at this
  exact this.symm

omit e in


public theorem bijective_smul_map_eqToHom {A B : X.Opens} (q : A = B) (t : L.val.obj (op A))
    (h : Function.Bijective (fun b : Γ(X, A) => b • t)) :
    Function.Bijective (fun a : Γ(X, B) => a • L.val.map (eqToHom q.symm : B ⟶ A).op t) := by
  subst q
  have e1 : L.val.map (eqToHom (rfl : A = A) : A ⟶ A).op t = t := by
    rw [eqToHom_refl, op_id]
    exact ModuleCat.InternalHom.map_id_apply (R := X.sheaf.obj) L.val _ _
  simpa only [e1] using h


public theorem trivSieve_mem (hL : Scheme.Modules.IsInvertible L) (V : X.Opens) :
    trivSieve L V ∈ Opens.grothendieckTopology X V := by
  intro x hx
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  refine ⟨V ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩

  let e' : (Modules.pullback (V ⊓ U).ι).obj L ≅ SheafOfModules.unit ((V ⊓ U : X.Opens) :
      Scheme.{u}).ringCatSheaf := trivializationOfLE_23d4f55a inf_le_right L eU
  exact ⟨trivializationBelow L ((restrictFunctor'IsoPullback (V ⊓ U)).app L ≪≫ e')⟩


public theorem isInvertible_dualSheaf (L : X.Modules) [Fact (Scheme.Modules.IsInvertible L)] :
    Scheme.Modules.IsInvertible (dualSheaf L) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (Fact.out : Scheme.Modules.IsInvertible L).1 x
  refine ⟨U, hxU, ⟨?_⟩⟩
  exact (λ_ _).symm ≪≫ (eU.symm ⊗ᵢ Iso.refl _) ≪≫
    Functor.Monoidal.μIso (Modules.pullback U.ι) L (dualSheaf L) ≪≫
    (Modules.pullback U.ι).mapIso (tensorDualSheafIso L) ≪≫
    pullbackTensorUnitObjIso U.ι

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in Scheme


public theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse_loc {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    ∃ M : X.Modules, AlgebraicGeometry.Scheme.Modules.IsInvertible M ∧
      Nonempty (L ⊗ M ≅ 𝟙_ X.Modules) :=
  haveI : Fact (Scheme.Modules.IsInvertible L) := ⟨hL⟩
  ⟨dualSheaf L, isInvertible_dualSheaf L, ⟨tensorDualSheafIso L⟩⟩

end LinkageInlined_23d4f55a

end InlinedTheorems

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard Scheme
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

end AlgebraicGeometry.RelPicard

end
