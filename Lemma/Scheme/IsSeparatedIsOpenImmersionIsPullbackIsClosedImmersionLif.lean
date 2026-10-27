import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {S Y' : (Scheme : Type (u + 1))} (f' : Y' ⟶ S)
private noncomputable def δ
  {P Q : (Scheme : Type (u + 1))} (jP : P ⟶ Y') (jQ : Q ⟶ Y') :
    pullback jP jQ ⟶ pullback (jP ≫ f') (jQ ≫ f') :=
  pullback.map jP jQ (jP ≫ f') (jQ ≫ f') (𝟙 P) (𝟙 Q) f' (Category.id_comp _).symm (Category.id_comp _).symm
private lemma isClosedImmersion_δ_self
  {P : (Scheme : Type (u + 1))} (j : P ⟶ Y') [Mono j]
  [IsClosedImmersion (pullback.diagonal (j ≫ f'))] : IsClosedImmersion (δ f' j j) := by
  let _ : IsIso (pullback.diagonal j) := inferInstance
  have h : δ f' j j = inv (pullback.diagonal j) ≫ pullback.diagonal (j ≫ f') := by
    rw [IsIso.eq_inv_comp]
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [δ, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
  rw [h]
  infer_instance
private lemma isClosedImmersion_δ_of_isPullback
  {A B U : (Scheme : Type (u + 1))} (jA : A ⟶ Y') (jB : B ⟶ Y')
  (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
  (hΓ : IsClosedImmersion (pullback.lift uA uB
    (by rw [← Category.assoc, hsq.w, Category.assoc]) : U ⟶ pullback (jA ≫ f') (jB ≫ f'))) :
    IsClosedImmersion (δ f' jA jB) := by
  have h1 : hsq.isoPullback.hom ≫ δ f' jA jB =
      pullback.lift uA uB (by rw [← Category.assoc, hsq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, Category.comp_id, IsPullback.isoPullback_hom_fst]
    · simp only [δ, Category.assoc, pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd]
  have h2 : δ f' jA jB = hsq.isoPullback.inv ≫
    pullback.lift uA uB (by rw [← Category.assoc, hsq.w, Category.assoc]) := by
    rw [← h1, Iso.inv_hom_id_assoc]
  rw [h2]
  infer_instance
private lemma isClosedImmersion_δ_symm
  {A B : (Scheme : Type (u + 1))} (jA : A ⟶ Y') (jB : B ⟶ Y')
  [IsClosedImmersion (δ f' jA jB)] : IsClosedImmersion (δ f' jB jA) := by
  have h : δ f' jB jA = (pullbackSymmetry jB jA).hom ≫ δ f' jA jB ≫ (pullbackSymmetry (jA ≫ f') (jB ≫ f')).hom := by
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  rw [h]
  infer_instance
/--
[AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift.lean)
-/
@[path]
private lemma main
  {S Y' A B U : (Scheme : Type (u + 1))} (f' : Y' ⟶ S)
    (jA : A ⟶ Y') (jB : B ⟶ Y') [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hcov : Set.range jA.base ∪ Set.range jB.base = Set.univ)
    (fA : A ⟶ S) (fB : B ⟶ S) (hA : jA ≫ f' = fA) (hB : jB ≫ f' = fB) [IsSeparated fA] [IsSeparated fB]
    (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
    (hΓ : IsClosedImmersion
      (pullback.lift uA uB (by rw [← hA, ← hB, ← Category.assoc, hsq.w, Category.assoc]) : U ⟶ pullback fA fB)) :
    IsSeparated f' := by
  classical
  subst hA hB
  let XU : Bool → (Scheme : Type (u + 1)) := fun b => cond b A B
  let fU : ∀ b : Bool, XU b ⟶ Y' := fun b => match b with
    | true => jA
    | false => jB
  have hfU : ∀ b : Bool, IsOpenImmersion (fU b) := by
    intro b
    cases b
    ·
      show IsOpenImmersion jB
      infer_instance
    ·
      show IsOpenImmersion jA
      infer_instance
  let 𝒰 : Y'.OpenCover := ⟨⟨Bool, XU, fU⟩, ⟨by
      simpa using show ∀ y : Y', ∃ (b : Bool) (x : XU b), (fU b).base x = y from fun y => by
        have hy : y ∈ Set.range jA.base ∪ Set.range jB.base := by
          rw [hcov]
          trivial
        obtain ⟨x, hx⟩ | ⟨x, hx⟩ := hy
        · exact ⟨true, x, hx⟩
        · exact ⟨false, x, hx⟩, by simpa using hfU⟩⟩
  have hδ : ∀ a b : Bool, IsClosedImmersion (δ f' (𝒰.f a) (𝒰.f b)) := by
    intro a b
    cases a
    ·
      cases b
      ·
        show IsClosedImmersion (δ f' jB jB)
        apply isClosedImmersion_δ_self f' jB
      ·
        show IsClosedImmersion (δ f' jB jA)
        let _ := isClosedImmersion_δ_of_isPullback f' jA jB uA uB hsq hΓ
        apply isClosedImmersion_δ_symm f' jA jB
    ·
      cases b
      ·
        show IsClosedImmersion (δ f' jA jB)
        apply isClosedImmersion_δ_of_isPullback f' jA jB uA uB hsq hΓ
      ·
        show IsClosedImmersion (δ f' jA jA)
        apply isClosedImmersion_δ_self f' jA
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f' f')
  rintro ⟨a, b⟩
  have hP := pullback_map_diagonal_isPullback (𝒰.f a) (𝒰.f b) f'
  have e : hP.isoPullback.hom ≫ pullback.snd _ _ = δ f' (𝒰.f a) (𝒰.f b) := hP.isoPullback_hom_snd
  have h3 : IsClosedImmersion (hP.isoPullback.hom ≫ pullback.snd _ _) := by
    rw [e]
    apply hδ a b
  refine (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hP.isoPullback.hom _).mp h3


-- created on 2026-10-20
