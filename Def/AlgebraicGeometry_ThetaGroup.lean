module
public import Mathlib
public import Def.AlgebraicGeometry_RiemannForm
public import Instance.AlgebraicGeometry_ThetaGroup
set_option autoImplicit false


public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra Scheme
  GoodReductionJacobian

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

universe v₁ u₁ v₂ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

def homMk {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base) (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) :
    X ⟶ Y := ⟨b, φ⟩

def sectionMk {X Y : ∫ᶜ F} (e : X.base ≅ Y.base) (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) :
    Y ⟶ X :=
  homMk e.inv
    ((F.mapId ⟨Opposite.op Y.base⟩).inv.toNatTrans.app Y.fiber ≫
      eqToHom (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, e.inv_hom_id]; rfl) ≫
      (F.mapComp e.hom.op.toLoc e.inv.op.toLoc).hom.toNatTrans.app Y.fiber ≫
      (F.map e.inv.op.toLoc).toFunctor.map φ.inv)

def isoMk {X Y : ∫ᶜ F} (e : X.base ≅ Y.base) (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) :
    X ≅ Y :=
  asIso (homMk e.hom φ.hom)

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace AlgebraicGeometry

def Scheme.Modules.fibration : Pseudofunctor (LocallyDiscrete (Scheme.{0}ᵒᵖ)) Cat.{0, 1} :=
  (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁

namespace RiemannForm

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
variable (L : RelativeGroupLaw k f)

variable (hc : L.IsCommutative)

def translationIso (P : L.AlgPoints hc k) : A ≅ A where
  hom := translation f L (RelativeGroupLaw.AlgPoints.toPoint P)
  inv := translation f L (RelativeGroupLaw.AlgPoints.toPoint (-P))
  hom_inv_id := by rw [← translation_toPoint_add, add_neg_cancel, translation_toPoint_zero]
  inv_hom_id := by rw [← translation_toPoint_add, neg_add_cancel, translation_toPoint_zero]

abbrev modulePair (M : A.Modules) : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration := ⟨A, M⟩

def thetaGroup (M : A.Modules) : Subgroup (Aut (modulePair (A := A) M) × Multiplicative (L.AlgPoints hc k)) where
  carrier := {g | g.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd g.2))}
  mul_mem' := by
    rintro ⟨a, P⟩ ⟨b, Q⟩ ha hb
    change (b ≪≫ a).hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (P * Q)))
    change a.hom.base = _ at ha
    change b.hom.base = _ at hb
    rw [toAdd_mul, add_comm, translation_toPoint_add, Iso.trans_hom, Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
      ha, hb]
  one_mem' := by
    change (Iso.refl (modulePair (A := A) M)).hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd 1))
    rw [toAdd_one, translation_toPoint_zero]
    rfl
  inv_mem' := by
    rintro ⟨a, P⟩ ha
    change a.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P)) at ha
    change a.symm.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P⁻¹))
    have h1 : a.hom.base ≫ a.inv.base = 𝟙 A := by
      rw [← Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, a.hom_inv_id]
      rfl
    rw [ha] at h1
    rw [Iso.symm_hom, toAdd_inv]
    haveI : Epi (translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P))) :=
      (inferInstance : Epi (translationIso f L hc (Multiplicative.toAdd P)).hom)
    exact (cancel_epi (translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P)))).1
      (h1.trans (translationIso f L hc (Multiplicative.toAdd P)).hom_inv_id.symm)

namespace thetaGroup

variable (M : A.Modules)

def pt : thetaGroup f L hc M →* Multiplicative (L.AlgPoints hc k) :=
  (MonoidHom.snd _ _).comp (thetaGroup f L hc M).subtype

def liftOfIso (z : L.AlgPoints hc k)
    (φ : (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint z))).obj M ≅ M) :
    thetaGroup f L hc M :=
  ⟨(Pseudofunctor.CoGrothendieck.isoMk (X := modulePair M) (Y := modulePair M) (translationIso f L hc z) φ.symm,
    Multiplicative.ofAdd z), rfl⟩

def unitReading {g : Aut (modulePair (A := A) M)} (h : g.hom.base = 𝟙 A) : M ⟶ M :=
  g.hom.fiber ≫ (Scheme.Modules.pullbackCongr h).hom.app M ≫ (Scheme.Modules.pullbackId A).hom.app M

def IsScalarElt (g : thetaGroup f L hc M) (c : k) : Prop :=
  ∃ hg : pt f L hc M g = 1, IsConstScalar f (unitReading M (base_eq_id_of_pt_eq_one f L hc M g hg)) c

end thetaGroup

def levelLift (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) :
    thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) :=
  thetaGroup.liftOfIso f L hc _ P (transportIso hx 𝓛)

end RiemannForm

end AlgebraicGeometry

end
