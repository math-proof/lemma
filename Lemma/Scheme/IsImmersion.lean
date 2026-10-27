import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isImmersion_respectsRight_isOpenImmersion :
  MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion := by
  refine ⟨fun i hi f hf => ?_⟩
  let _ := hi
  let _ := hf
  infer_instance
private lemma surjective_app_of_eq
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) (U V : Y.Opens) (e : V = U)
  (hs : Function.Surjective (f.app U)) :
  Function.Surjective (f.app V) := by
  subst e
  apply hs
private lemma isClosedImmersion_morphismRestrict_of_surjective
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y)
  (U : Y.Opens) (hU : IsAffineOpen U) (hfU : IsAffineOpen ((TopologicalSpace.Opens.map f.base).obj U))
  (hs : Function.Surjective (f.app U)) :
  IsClosedImmersion (morphismRestrict f U) := by
  let _ : IsAffine U := hU
  let _ : IsAffine ((TopologicalSpace.Opens.map f.base).obj U) := hfU
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]
  refine ⟨hfU, ?_⟩
  rw [morphismRestrict_appTop]
  have e : U.ι ''ᵁ ⊤ = U := by simp [Scheme.Hom.image_top_eq_opensRange]
  have h1 : Function.Surjective (f.app (U.ι ''ᵁ ⊤)) := surjective_app_of_eq f U _ e hs
  have h2 : Function.Surjective
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨z, rfl⟩ := h2 y
  obtain ⟨x, rfl⟩ := h1 z
  refine ⟨x, ConcreteCategory.comp_apply _ _ _⟩
private lemma isImmersion_of_affine_charts
  {Y P : (Scheme : Type (u + 1))} (φ : Y ⟶ P) {J : Type*} (W : J → P.Opens)
  (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen ((TopologicalSpace.Opens.map φ.base).obj (W j)))
    (hcov : ⨆ j, (TopologicalSpace.Opens.map φ.base).obj (W j) = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ := by
  let _ := isImmersion_respectsRight_isOpenImmersion
  have hrange : Set.range φ.base ⊆ ((⨆ j, W j : P.Opens) : Set P) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ (⨆ j, (TopologicalSpace.Opens.map φ.base).obj (W j) : Y.Opens) := by
      rw [hcov]
      trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨j, hj⟩ := hy
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    refine ⟨j, hj⟩
  have himm : ∀ j, IsImmersion (morphismRestrict φ (W j)) := by
    intro j
    let _ := isClosedImmersion_morphismRestrict_of_surjective φ (W j) (hWaff j) (hYaff j) (hsurj j)
    infer_instance
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) W hrange himm
/--
[AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.lean)
-/
@[path]
private lemma main
  {Y P : (Scheme : Type 1)} (φ : Y ⟶ P) {J : Type} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen ((TopologicalSpace.Opens.map φ.base).obj (W j)))
    (hcov : ⨆ j, (TopologicalSpace.Opens.map φ.base).obj (W j) = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
  -- imply
  IsImmersion φ := by
  -- proof
  apply isImmersion_of_affine_charts φ W hWaff hYaff hcov hsurj


-- created on 2026-10-20
