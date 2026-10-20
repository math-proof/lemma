import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.lean)
-/
@[path]
private lemma main
  {σ : Type u} (H : σ → (Scheme : Type (u + 1))) {T : (Scheme : Type (u + 1))} (U : σ → T.Opens)
  (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤)
  (v : ∀ i, ((U i : T.Opens) : (Scheme : Type (u + 1))) ⟶ H i) :
  -- imply
  ∃! u : T ⟶ ∐ H, ∀ i, (U i).ι ≫ u = v i ≫ Sigma.ι H i := by
  -- proof
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover U (IsOpenCover.mk hcov)
  have hcompat : ∀ i j : σ, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (v i ≫ Sigma.ι H i) = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (v j ≫ Sigma.ι H j) := by
    intro i j
    if hij : i = j then
      subst hij
      rw [fst_eq_snd_of_mono_eq]
    else
      let _ : IsEmpty ↥(pullback (𝒰.f i) (𝒰.f j)) := by
        refine ⟨fun x => ?_⟩
        have hx : (pullback.fst (𝒰.f i) (𝒰.f j)).base x ∈ Set.range (pullback.fst (𝒰.f i) (𝒰.f j)).base := ⟨x, rfl⟩
        rw [Scheme.Pullback.range_fst] at hx
        obtain ⟨y, hy⟩ := hx
        have h1 : ((𝒰.f i).base ((pullback.fst (𝒰.f i) (𝒰.f j)).base x)) ∈ (U i : Set T) := by
          simp only [Scheme.openCoverOfIsOpenCover_f, 𝒰]
          apply Subtype.property _
        have h2 : ((𝒰.f j).base y) ∈ (U j : Set T) := by
          simp only [Scheme.openCoverOfIsOpenCover_f, 𝒰]
          apply Subtype.property _
        rw [hy] at h2
        apply Set.disjoint_iff.mp (Opens.coe_disjoint.mpr (hdisj i j hij)) ⟨h1, h2⟩
      apply (isInitialOfIsEmpty).hom_ext _ _
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 (fun i => v i ≫ Sigma.ι H i) hcompat, fun i => ?_, fun u' hu' => ?_⟩
  · apply Scheme.Cover.ι_glueMorphisms 𝒰 _ hcompat i
  ·
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms 𝒰 _ hcompat i]
    apply hu' i


-- created on 2026-10-20
