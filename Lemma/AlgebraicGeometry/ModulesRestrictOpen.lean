import Mathlib
import Def.AlgebraicGeometry_ModulesRestrictOpen

set_option autoImplicit false

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

namespace PresheafOfModules

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G H : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}
  (φ : T ⟶ G.op ⋙ S)


@[simp] lemma pushforwardNatTrans_app_app_apply (α : F ⟶ G) (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl


@[simp] lemma pushforwardCongr_hom_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).hom.app M).app U x = x := by subst e; rfl

@[simp] lemma pushforwardCongr_inv_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).inv.app M).app U x = x := by subst e; rfl

end NatTrans

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)


lemma pushforwardPushforwardAdj_unit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app U x =
      M.map (adj.counit.app U.unop).op x := rfl

lemma pushforwardPushforwardAdj_counit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).app U x =
      M.map (adj.unit.app U.unop).op x := rfl

end Adjunction

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}} (U : X.Opens)


lemma restrictPresheaf_obj_obj (P : X.PresheafOfModules) (V : (U : Scheme.{u}).Opensᵒᵖ) :
    (((restrictPresheaf U).obj P).obj V : Type u) = P.obj (Opposite.op (U.ι ''ᵁ V.unop)) := rfl


lemma restrictOpen_obj_val (M : X.Modules) :
    ((restrictOpen U).obj M).val = (restrictPresheaf U).obj M.val := rfl

end AlgebraicGeometry.Scheme.Modules
