import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isTorsionFree_sections
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} (g : X ⟶ Spec (CommRingCat.of R)) [Flat g]
  (W : X.Opens) :
    let _ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ W le_top).hom.toAlgebra
    Module.IsTorsionFree R (X.presheaf.obj (op W)) := by
  let _ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ W le_top).hom.toAlgebra
  let ι := Subtype (fun V : X.affineOpens => V.1 ≤ W)
  let U : ι → X.Opens := fun V => V.1.1
  have hcover : W ≤ iSup U := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
    apply Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  let _ : ∀ V : ι, Algebra R (X.presheaf.obj (op (U V))) := fun V =>
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ (U V) le_top).hom.toAlgebra
  let _ : ∀ V : ι, Module.Flat R (X.presheaf.obj (op (U V))) := fun V => by
    apply (RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv (g.appLE ⊤ (U V) le_top)).mpr (g.flat_appLE (isAffineOpen_top _) V.1.2 (le_top : U V ≤ (TopologicalSpace.Opens.map g.base).obj ⊤))
  let ρ : X.presheaf.obj (op W) → ∀ V : ι, X.presheaf.obj (op (U V)) := fun s V => X.presheaf.map (homOfLE V.2).op s
  have hρ : Function.Injective ρ := fun s t h =>
    X.sheaf.eq_of_locally_eq' U W (fun V => homOfLE V.2) hcover s t (fun V => congrFun h V)
  refine hρ.moduleIsTorsionFree ρ ?_
  intro r s
  funext V
  change X.presheaf.map (homOfLE V.2).op (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ W le_top) r * s) = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ (U V) le_top) r * X.presheaf.map (homOfLE V.2).op s
  rw [map_mul, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

/--
[AlgebraicGeometry_flat_image_comp_of_isDedekindDomain](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDedekindDomain R]
  {X J : (Scheme : Type (u + 1))} (σ : X ⟶ J) [QuasiCompact σ] (f : J ⟶ Spec (CommRingCat.of R)) [Flat (σ ≫ f)] :
    Flat (σ.imageι ≫ f) := by
  let U : J.affineOpens → σ.image.affineOpens := fun V => ⟨(TopologicalSpace.Opens.map σ.imageι.base).obj V.1, V.2.preimage σ.imageι⟩
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) U ?_ ?_
  ·
    rw [← top_le_iff]
    intro b _
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, _⟩ := J.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (σ.imageι b)) isOpen_univ
    apply Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hbV⟩
  ·
    intro V
    rw [← RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    let ψ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.imageι ≫ f).appLE ⊤ (U V).1 le_top
    let _ := ψ.hom.toAlgebra
    change Module.Flat R ((σ.image).presheaf.obj (op (U V).1))
    let _ : Flat (σ.toImage ≫ σ.imageι ≫ f) := by
      rw [Scheme.Hom.toImage_imageι_assoc]
      infer_instance
    let W : X.Opens := (TopologicalSpace.Opens.map σ.toImage.base).obj (U V).1
    let _ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.toImage ≫ σ.imageι ≫ f).appLE ⊤ W le_top).hom.toAlgebra
    let _ : Module.IsTorsionFree R (X.presheaf.obj (op W)) := isTorsionFree_sections (σ.toImage ≫ σ.imageι ≫ f) W
    have hinj : Function.Injective (σ.toImage.app (U V).1) := σ.toImage_app_injective V
    let _ : Module.IsTorsionFree R ((σ.image).presheaf.obj (op (U V).1)) := by
      refine hinj.moduleIsTorsionFree (σ.toImage.app (U V).1) ?_
      intro r s
      change σ.toImage.app (U V).1 (ψ r * s) = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.toImage ≫ σ.imageι ≫ f).appLE ⊤ W le_top) r * σ.toImage.app (U V).1 s
      rw [map_mul, ← CommRingCat.comp_apply]
      have hc : ψ ≫ σ.toImage.app (U V).1 = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.toImage ≫ σ.imageι ≫ f).appLE ⊤ W le_top := by
        change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (σ.imageι ≫ f).appLE ⊤ (U V).1 le_top) ≫ σ.toImage.app (U V).1 = _
        rw [Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      rw [hc]
    infer_instance


-- created on 2026-10-20
