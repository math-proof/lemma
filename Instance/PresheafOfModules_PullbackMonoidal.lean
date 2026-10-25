-- Carved from Lemma/Definitions/Def_PresheafOfModules_PullbackMonoidal.lean: instance decls only.
import Mathlib
import Lemma.PresheafOfModules.PullbackMonoidal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u v₁ u₁ v₂ u₂

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

section restrictScalars

variable {C : Type u₁} [Category.{v₁} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)

noncomputable instance restrictScalars_laxMonoidal :
    (restrictScalars (ringCatHom φ)).LaxMonoidal where
  ε := restrictScalarsε φ
  μ M N := restrictScalarsμ φ M N
  μ_natural_left f N := by
    ext1 U
    simp only [comp_app, whiskerRight_app, restrictScalars_map_app]
    exact μ_natural_left (restrictScalarsAt φ U) (f.app U) (N.obj U)
  μ_natural_right M f := by
    ext1 U
    simp only [comp_app, whiskerLeft_app, restrictScalars_map_app]
    exact μ_natural_right (restrictScalarsAt φ U) (M.obj U) (f.app U)
  associativity M N P := by
    ext1 U
    simp only [comp_app, whiskerRight_app, whiskerLeft_app, restrictScalars_map_app,
      associator_hom_app]
    exact associativity (restrictScalarsAt φ U) (M.obj U) (N.obj U) (P.obj U)
  left_unitality M := by
    ext1 U
    simp only [comp_app, whiskerRight_app, restrictScalars_map_app, leftUnitor_hom_app]
    exact left_unitality (restrictScalarsAt φ U) (M.obj U)
  right_unitality M := by
    ext1 U
    simp only [comp_app, whiskerLeft_app, restrictScalars_map_app, rightUnitor_hom_app]
    exact right_unitality (restrictScalarsAt φ U) (M.obj U)

end restrictScalars

section pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

noncomputable instance pushforward_laxMonoidal :
    (pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).LaxMonoidal :=
  inferInstanceAs (pushforward₀OfCommRingCat F R ⋙
    restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).LaxMonoidal

noncomputable instance pullback_oplaxMonoidal
    [(pushforward (R := R ⋙ forget₂ _ _) (ringCatHom φ)).IsRightAdjoint] :
    (pullback (R := R ⋙ forget₂ _ _) (ringCatHom φ)).OplaxMonoidal :=
  (pullbackPushforwardAdjunction (R := R ⋙ forget₂ _ _) (ringCatHom φ)).leftAdjointOplaxMonoidal

end pushforward

end PresheafOfModules


namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

noncomputable instance free_monoidal : (free R').Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := freeεIso
      μIso := freeμIso
      μIso_hom_natural_left := fun {F F'} f G => by
        ext1 X
        simp only [comp_app, whiskerRight_app, free_map_app, freeμIso_hom_app,
          Monoidal.whiskerRight_app]
        exact μ_natural_left (ModuleCat.free (R.obj X)) (f.app X) (G.obj X)
      μIso_hom_natural_right := fun {F F'} G f => by
        ext1 X
        simp only [comp_app, whiskerLeft_app, free_map_app, freeμIso_hom_app,
          Monoidal.whiskerLeft_app]
        exact μ_natural_right (ModuleCat.free (R.obj X)) (G.obj X) (f.app X)
      associativity := fun F G H => by
        ext1 X
        simp only [comp_app, whiskerRight_app, whiskerLeft_app, free_map_app, freeμIso_hom_app,
          associator_hom_app, Monoidal.associator_hom_app]
        exact associativity (ModuleCat.free (R.obj X)) (F.obj X) (G.obj X) (H.obj X)
      left_unitality := fun F => by
        ext1 X
        simp only [comp_app, whiskerRight_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
          leftUnitor_hom_app, Monoidal.leftUnitor_hom_app]
        exact left_unitality (ModuleCat.free (R.obj X)) (F.obj X)
      right_unitality := fun F => by
        ext1 X
        simp only [comp_app, whiskerLeft_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
          rightUnitor_hom_app, Monoidal.rightUnitor_hom_app]
        exact right_unitality (ModuleCat.free (R.obj X)) (F.obj X) }

end PresheafOfModules

namespace PresheafOfModules

namespace PullbackMonoidal

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

instance isIso_δ_gS (U V : C) : IsIso (δ (pb F φ) (gS U) (gS V)) := by
  have h : δ (pb F φ) (gS U) (gS V) =
      ((pb F φ).map (j (S := S) U V).hom ≫ (e F φ (U ⨯ V)).hom ≫ (r (R := R) F U V).hom) ≫
        inv ((e F φ U).hom ⊗ₘ (e F φ V).hom) := by
    rw [← δ_gS_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

instance : PreservesColimitsOfSize.{u, u} (pb F φ) := (adj F φ).leftAdjoint_preservesColimits

instance isIso_δ (A B : PresheafOfModules.{u} S') : IsIso (δ (pb F φ) A B) := by

  have h1 : ∀ (U : C) (B : PresheafOfModules.{u} S'), IsIso (δ (pb F φ) (gS U) B) := fun U => by
    let σ : tensorLeft (gS (S := S) U) ⋙ pb F φ ⟶ pb F φ ⋙ tensorLeft ((pb F φ).obj (gS U)) :=
      { app := fun B => δ (pb F φ) (gS U) B
        naturality := fun B B' g => (δ_natural_right (pb F φ) (gS U) g).symm }
    exact isIso_app_of_freeYoneda (S := S) σ (fun V => isIso_δ_gS F φ U V)

  let τ : tensorRight B ⋙ pb F φ ⟶ pb F φ ⋙ tensorRight ((pb F φ).obj B) :=
    { app := fun A => δ (pb F φ) A B
      naturality := fun A A' f => (δ_natural_left (pb F φ) f B).symm }
  exact isIso_app_of_freeYoneda (S := S) τ (fun U => h1 U B) A

instance isIso_η : IsIso (η (pb F φ)) := by rw [η_eq]; infer_instance

noncomputable instance pullback_monoidal : (pb F φ).Monoidal := Functor.Monoidal.ofOplaxMonoidal _

end PullbackMonoidal

noncomputable instance pullback_monoidal' {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteProducts C] [HasFiniteProducts D] (F : C ⥤ D) [PreservesFiniteProducts F]
    {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R) :
    (pullback (R := R ⋙ forget₂ _ _) (ringCatHom φ)).Monoidal :=
  PullbackMonoidal.pullback_monoidal F φ

end PresheafOfModules
