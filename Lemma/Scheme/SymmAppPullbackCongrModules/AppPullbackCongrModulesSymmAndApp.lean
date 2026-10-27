import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_Modules_pullback_iso_trans_eq_of_cocycle](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullback_iso_trans_eq_of_cocycle.lean)
-/
@[path]
private lemma main
  (X' X'' X''' : (Scheme : Type (u + 1)))
  (a₁ a₂ : X'' ⟶ X')
  (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
  (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁)
  (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁)
  (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
  (L' : X'.Modules)
  (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
  (hψ : ((((((((((Scheme.Modules.pullbackCongr h₁).app L').symm.trans (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm)).trans ((Scheme.Modules.pullback b₁₂).mapIso ψ)).trans (((Scheme.Modules.pullbackComp b₁₂ a₂).app L'))).trans (((Scheme.Modules.pullbackCongr h₂).app L'))).trans (((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm)).trans ((Scheme.Modules.pullback b₂₃).mapIso ψ)).trans (((Scheme.Modules.pullbackComp b₂₃ a₂).app L'))).trans (((Scheme.Modules.pullbackCongr h₃).app L').symm))=((((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm.trans ((Scheme.Modules.pullback b₁₃).mapIso ψ)).trans (((Scheme.Modules.pullbackComp b₁₃ a₂).app L')))) :
  ((((Scheme.Modules.pullbackCongr h₁).app L').symm.trans ((((((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm.trans ((Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')))).trans ((Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))))))= (((((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm.trans ((Scheme.Modules.pullback b₁₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')))).trans ((((((Scheme.Modules.pullbackComp b₁₃ a₁).app L').trans (((Scheme.Modules.pullbackCongr h₁).app L').symm)).trans (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm))))))) ∧ ((((Scheme.Modules.pullbackCongr h₂).app L').symm.trans ((((((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm.trans ((Scheme.Modules.pullback b₁₂).mapIso ψ.symm)).trans ((Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))))))= (((((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm.trans ((Scheme.Modules.pullback b₂₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')))).trans (((((((Scheme.Modules.pullbackComp b₂₃ a₁).app L').trans (((Scheme.Modules.pullbackCongr h₂).app L').symm)).trans (((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm)).trans ((Scheme.Modules.pullback b₁₂).mapIso ψ.symm))))))) ∧ ((((Scheme.Modules.pullbackCongr h₃).app L').symm.trans ((((((Scheme.Modules.pullbackComp b₁₃ a₂).app L').symm.trans ((Scheme.Modules.pullback b₁₃).mapIso ψ.symm)).trans ((((((Scheme.Modules.pullbackComp b₁₃ a₁).app L').trans (((Scheme.Modules.pullbackCongr h₁).app L').symm)).trans (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm))))))))= (((((Scheme.Modules.pullbackComp b₂₃ a₂).app L').symm.trans ((Scheme.Modules.pullback b₂₃).mapIso ψ.symm)).trans (((((((Scheme.Modules.pullbackComp b₂₃ a₁).app L').trans (((Scheme.Modules.pullbackCongr h₂).app L').symm)).trans (((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm)).trans ((Scheme.Modules.pullback b₁₂).mapIso ψ.symm))))))) := by
  have Pih : ∀ {Y Z W : (Scheme : Type (u + 1))} {T : Y.Modules} (g : Y ⟶ Z) (f : Z ⟶ W) (M : W.Modules) (k : (Scheme.Modules.pullback (g ≫ f)).obj M ⟶ T), (Scheme.Modules.pullbackComp g f).inv.app M ≫ (Scheme.Modules.pullbackComp g f).hom.app M ≫ k = k :=
    fun g f M k => Iso.inv_hom_id_app_assoc _ _ _
  dsimp [Functor.comp_obj] at Pih
  have hinv := congrArg Iso.inv hψ
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hinv
  dsimp [Functor.comp_obj] at hinv
  have hinv_w {N : X'''.Modules} (k : (Scheme.Modules.pullback (b₁₃ ≫ a₁)).obj L' ⟶ N) :
    (Scheme.Modules.pullbackComp b₁₃ a₂).inv.app L' ≫ (Scheme.Modules.pullback b₁₃).map ψ.inv ≫ (Scheme.Modules.pullbackComp b₁₃ a₁).hom.app L' ≫ k = (Scheme.Modules.pullbackCongr h₃).hom.app L' ≫ (Scheme.Modules.pullbackComp b₂₃ a₂).inv.app L' ≫ (Scheme.Modules.pullback b₂₃).map ψ.inv ≫ (Scheme.Modules.pullbackComp b₂₃ a₁).hom.app L' ≫ (Scheme.Modules.pullbackCongr h₂).inv.app L' ≫ (Scheme.Modules.pullbackComp b₁₂ a₂).inv.app L' ≫ (Scheme.Modules.pullback b₁₂).map ψ.inv ≫ (Scheme.Modules.pullbackComp b₁₂ a₁).hom.app L' ≫ (Scheme.Modules.pullbackCongr h₁).hom.app L' ≫ k := by
    simpa [Category.assoc] using congrArg (fun e => e ≫ k) hinv.symm
  refine ⟨Iso.ext ?_, Iso.ext ?_, Iso.ext ?_⟩
  ·
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id, Iso.app_hom, Iso.app_inv]
    dsimp [Functor.comp_obj]
    simp only [Category.assoc, Category.comp_id, Pih]
  ·
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id, Iso.app_hom, Iso.app_inv]
    dsimp [Functor.comp_obj]
    simp only [Category.assoc, Category.comp_id, Pih]
  ·
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
    dsimp [Functor.comp_obj]
    simp only [Category.assoc, hinv_w, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    dsimp [Functor.comp_obj]
    simp only [Category.comp_id]


-- created on 2026-10-20
