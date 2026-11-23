module

public import Mathlib
public import Def.AlgebraicGeometry_RiemannForm
public import Instance.AlgebraicGeometry_ThetaGroup

public noncomputable section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra Scheme
  GoodReductionJacobian

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

universe v₁ u₁ v₂ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}


@[simp] public theorem homMk_base {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) : (homMk b φ).base = b := rfl

@[simp] public theorem homMk_fiber {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) : (homMk b φ).fiber = φ := rfl


public theorem mono_homMk {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base) [Mono b]
    (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) [IsIso φ] : Mono (homMk b φ) := by
  refine ⟨fun {W} u v h => ?_⟩
  obtain ⟨ub, uf⟩ := u
  obtain ⟨vb, vf⟩ := v
  have hb : ub = vb := by
    have := congrArg Hom.base h
    simp only [categoryStruct_comp_base, homMk_base] at this
    exact (cancel_mono b).1 this
  subst hb
  have hf := Hom.congr h
  simp only [categoryStruct_comp_fiber, homMk_base, homMk_fiber, eqToHom_refl, Category.comp_id] at hf
  have hb1 : (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber ≫
      (F.mapComp b.op.toLoc ub.op.toLoc).hom.toNatTrans.app Y.fiber = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app]
  have hb2 : (F.mapComp b.op.toLoc ub.op.toLoc).hom.toNatTrans.app Y.fiber ≫
      (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]
  haveI : IsIso ((F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber) := ⟨⟨_, hb1, hb2⟩⟩
  have hf2 : (uf ≫ (F.map ub.op.toLoc).toFunctor.map φ) ≫ (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber =
      (vf ≫ (F.map ub.op.toLoc).toFunctor.map φ) ≫ (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber := by
    simp only [Category.assoc]
    exact hf
  have hf3 := (cancel_mono ((F.map ub.op.toLoc).toFunctor.map φ)).1
    ((cancel_mono ((F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber)).1 hf2)
  subst hf3
  rfl


public theorem sectionMk_comp {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) :
    sectionMk e φ ≫ homMk e.hom φ.hom = 𝟙 Y := by
  apply Hom.ext _ _ (by simp [sectionMk, homMk])
  simp only [sectionMk, categoryStruct_comp_fiber, homMk_base, homMk_fiber, categoryStruct_id_fiber, Category.assoc]
  have h2 : (F.map e.inv.op.toLoc).toFunctor.map φ.inv ≫ (F.map e.inv.op.toLoc).toFunctor.map φ.hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  have h3 : (F.mapComp e.hom.op.toLoc e.inv.op.toLoc).hom.toNatTrans.app Y.fiber ≫
      (F.mapComp e.hom.op.toLoc e.inv.op.toLoc).inv.toNatTrans.app Y.fiber = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]
  erw [reassoc_of% h2, h3]
  erw [Category.comp_id]
  rfl


@[simp] public theorem isoMk_hom {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : (isoMk e φ).hom = homMk e.hom φ.hom := rfl


public theorem isoMk_hom_base {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : (isoMk e φ).hom.base = e.hom := rfl


public theorem isoMk_hom_fiber {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : (isoMk e φ).hom.fiber = φ.hom := rfl

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace AlgebraicGeometry


@[simp] public theorem Scheme.Modules.fibration_obj (X : Scheme.{0}) :
    (Scheme.Modules.fibration.obj ⟨Opposite.op X⟩ : Type 1) = X.Modules := rfl


@[simp] public theorem Scheme.Modules.fibration_map_toFunctor {X Y : Scheme.{0}} (g : X ⟶ Y) :
    (Scheme.Modules.fibration.map g.op.toLoc).toFunctor = Scheme.Modules.pullback g := rfl

namespace RiemannForm

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
variable (L : RelativeGroupLaw k f)


public theorem constPt_eq_schemeHomOverComp (x : Pt f) :
    constPt f x = schemeHomOverComp f (by rw [specMap_algebraMap_self, Category.comp_id]) x :=
  Subtype.ext rfl


public theorem translation_one : translation f L (L.one _) = 𝟙 A := by
  unfold translation
  rw [constPt_eq_schemeHomOverComp, L.one_natural, L.mul_one]


public theorem translation_mul (x y : Pt f) :
    translation f L (L.mul _ x y) = translation f L x ≫ translation f L y := by
  have hx := translation_over f L x
  have e1 : translation f L x ≫ translation f L y =
      (schemeHomOverComp (translation f L x) hx (L.mul f RelativeGroupLaw.idPoint (constPt f y))).1 := rfl
  rw [e1, L.mul_natural]
  have e2 : schemeHomOverComp (translation f L x) hx RelativeGroupLaw.idPoint =
      L.mul f RelativeGroupLaw.idPoint (constPt f x) := Subtype.ext (Category.comp_id _)
  have e3 : schemeHomOverComp (translation f L x) hx (constPt f y) = constPt f y :=
    Subtype.ext (show translation f L x ≫ (f ≫ y.1) = f ≫ y.1 by rw [← Category.assoc, hx])
  rw [e2, e3, L.mul_assoc]
  unfold translation
  rw [constPt_eq_schemeHomOverComp f (L.mul _ x y), L.mul_natural, ← constPt_eq_schemeHomOverComp,
    ← constPt_eq_schemeHomOverComp]

variable (hc : L.IsCommutative)


public theorem translation_toPoint_zero :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) = 𝟙 A :=
  translation_one f L


public theorem translation_toPoint_add (P Q : L.AlgPoints hc k) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)) =
      translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q) :=
  translation_mul f L _ _


@[simp] public theorem translationIso_hom (P : L.AlgPoints hc k) :
    (translationIso f L hc P).hom = translation f L (RelativeGroupLaw.AlgPoints.toPoint P) := rfl


@[simp] public theorem modulePair_base (M : A.Modules) : (modulePair (A := A) M).base = A := rfl

@[simp] public theorem modulePair_fiber (M : A.Modules) : (modulePair (A := A) M).fiber = M := rfl


@[simp] public theorem pt_apply (g : thetaGroup f L hc M) : pt f L hc M g = g.1.2 := rfl


public theorem base_eq (g : thetaGroup f L hc M) :
    g.1.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd g.1.2)) :=
  g.2


public theorem base_eq_id_of_pt_eq_one (g : thetaGroup f L hc M) (hg : pt f L hc M g = 1) :
    g.1.1.hom.base = 𝟙 A := by
  rw [base_eq, ← pt_apply, hg, toAdd_one, translation_toPoint_zero]


@[simp] public theorem pt_liftOfIso (z : L.AlgPoints hc k)
    (φ : (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint z))).obj M ≅ M) :
    pt f L hc M (liftOfIso f L hc M z φ) = Multiplicative.ofAdd z := rfl


public theorem liftOfIso_hom_fiber (z : L.AlgPoints hc k)
    (φ : (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint z))).obj M ≅ M) :
    (liftOfIso f L hc M z φ).1.1.hom.fiber = φ.inv := rfl


@[simp] public theorem pt_levelLift (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) :
    thetaGroup.pt f L hc _ (levelLift f L hc 𝓛 n P hx) = Multiplicative.ofAdd P := rfl

end RiemannForm

end AlgebraicGeometry

end
