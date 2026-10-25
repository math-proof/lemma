import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Building.AptFoldingFromRetraction
open AptFoldingFromRetraction
open scoped Classical


/--
[exists_canonical_retraction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptFoldingFromRetraction.lean)
-/
@[path]
lemma exists_canonical_retraction
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C) :
-- imply
  ∃ (ρ : V → V), (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ ∈ A.faces) ∧ (∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ v = v) ∧ (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → A.IsMaximal (D.image ρ)) ∧ (∀ D₁ D₂, b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂ → D₁.image ρ = D₂.image ρ ∨ A.Adjacent (D₁.image ρ) (D₂.image ρ)) ∧ (∀ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments → C ∈ B.faces → ∀ v₁ v₂, (∃ s ∈ B.faces, v₁ ∈ s) → (∃ s ∈ B.faces, v₂ ∈ s) → ρ v₁ = ρ v₂ → v₁ = v₂) := by
-- proof
  have hC_K := b.apartmentSystem.maximal_in_apt_is_maximal A hA C hC
  obtain ⟨ρ, hρ_simp, hρ_fix, _, hρ_iso, _⟩ :=
    _root_.exists_canonical_retraction b A hA C hC.1 hC_K
  have img_eq : ∀ s ∈ A.faces, s.image ρ = s := by
    intro s hs; ext v; simp only [Finset.mem_image]
    exact ⟨fun ⟨w, hw, he⟩ => he ▸ (hρ_fix w ⟨s, hs, hw⟩).symm ▸ hw,
      fun hv => ⟨v, hv, hρ_fix v ⟨s, hs, hv⟩⟩⟩
  have A_sub_B : ∀ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments →
    C ∈ B.faces → ∀ s ∈ A.faces, s ∈ B.faces := by
    intro B hB hC_B s hs
    have h1 : s.image ρ ∈ A.faces := by rw [img_eq s hs]; exact hs
    exact ((hρ_iso B hB hC_B).2 s).mpr h1
  have inj_lift : ∀ (B : SimplicialComplex V) (hB : B ∈ b.apartmentSystem.apartments)
    (hC_B : C ∈ B.faces) (D y : Finset V), D ∈ B.faces → y ∈ B.faces →
    y.image ρ = y → D.image ρ ⊆ y → D ⊆ y := by
    intro B hB hC_B D y _ _ hy_img hle v hv
    have hρv_in_y : ρ v ∈ y := hle (Finset.mem_image_of_mem ρ hv)
    rw [← hy_img] at hρv_in_y
    rw [Finset.mem_image] at hρv_in_y
    obtain ⟨w, hw, hρw_eq⟩ := hρv_in_y
    exact (hρ_iso B hB hC_B).1 hρw_eq.symm ▸ hw
  have img_maximal : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
    A.IsMaximal (D.image ρ) := by
    intro D hD_max
    constructor
    · exact hρ_simp D hD_max.1
    · intro y hy hle
      obtain ⟨B, hB, hC_B, hD_B⟩ := b.apartmentSystem.contains_pair C D hC_K hD_max
      have hy_B : y ∈ B.faces := A_sub_B B hB hC_B y hy
      have hy_img : y.image ρ = y := img_eq y hy
      have hD_sub_y : D ⊆ y := inj_lift B hB hC_B D y hD_B hy_B hy_img hle
      have hD_B_max : B.IsMaximal D :=
        ⟨hD_B, fun z hz hsub => hD_max.2 z (b.apartmentSystem.sub B hB hz) hsub⟩
      have hDy : D = y := hD_B_max.2 y hy_B hD_sub_y
      rw [hDy, hy_img]
  refine ⟨ρ, hρ_simp, hρ_fix, img_maximal, ?_, ?_⟩
  ·
    intro D₁ D₂ hadj
    obtain ⟨hD₁_max, hD₂_max, hne, F, hF₁, hF₂⟩ := hadj
    by_cases heq : D₁.image ρ = D₂.image ρ
    · left; exact heq
    · right
      have hD₁_img_max : A.IsMaximal (D₁.image ρ) := img_maximal D₁ hD₁_max
      have hD₂_img_max : A.IsMaximal (D₂.image ρ) := img_maximal D₂ hD₂_max
      have hF_img : F.image ρ ∈ A.faces := hρ_simp F hF₁.1.1
      have hF_sub₁ : F.image ρ ⊆ D₁.image ρ :=
        Finset.image_subset_image hF₁.1.2.2
      have hF_sub₂ : F.image ρ ⊆ D₂.image ρ :=
        Finset.image_subset_image hF₂.1.2.2
      obtain ⟨B₁, hB₁, hC_B₁, hD₁_B₁⟩ := b.apartmentSystem.contains_pair C D₁ hC_K hD₁_max
      have hiso₁ := hρ_iso B₁ hB₁ hC_B₁
      have hcard₁ : (D₁.image ρ \ F.image ρ).card = 1 := by
        have h1 : (D₁.image ρ).card = D₁.card :=
          Finset.card_image_of_injective D₁ hiso₁.1
        have h2 : (F.image ρ).card = F.card :=
          Finset.card_image_of_injective F hiso₁.1
        have h3 := Finset.card_sdiff_add_card_inter (D₁.image ρ) (F.image ρ)
        have h4 := Finset.card_sdiff_add_card_inter D₁ F
        rw [Finset.inter_eq_right.mpr hF_sub₁] at h3
        rw [Finset.inter_eq_right.mpr hF₁.1.2.2] at h4
        linarith [hF₁.2]
      obtain ⟨B₂, hB₂, hC_B₂, hD₂_B₂⟩ := b.apartmentSystem.contains_pair C D₂ hC_K hD₂_max
      have hiso₂ := hρ_iso B₂ hB₂ hC_B₂
      have hcard₂ : (D₂.image ρ \ F.image ρ).card = 1 := by
        have h1 : (D₂.image ρ).card = D₂.card :=
          Finset.card_image_of_injective D₂ hiso₂.1
        have h2 : (F.image ρ).card = F.card :=
          Finset.card_image_of_injective F hiso₂.1
        have h3 := Finset.card_sdiff_add_card_inter (D₂.image ρ) (F.image ρ)
        have h4 := Finset.card_sdiff_add_card_inter D₂ F
        rw [Finset.inter_eq_right.mpr hF_sub₂] at h3
        rw [Finset.inter_eq_right.mpr hF₂.1.2.2] at h4
        linarith [hF₂.2]
      exact ⟨hD₁_img_max, hD₂_img_max, heq, F.image ρ,
        ⟨⟨hF_img, hD₁_img_max.1, hF_sub₁⟩, hcard₁⟩,
        ⟨⟨hF_img, hD₂_img_max.1, hF_sub₂⟩, hcard₂⟩⟩
  ·
    intro B hB hC_B v₁ v₂ _ _ heq
    exact (hρ_iso B hB hC_B).1 heq


private lemma apt_is_thin
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments) :
-- imply
  ∀ F C, A.IsFacet F C → A.IsMaximal C → ∃! D, D ≠ C ∧ A.IsFacet F D ∧ A.IsMaximal D := by
-- proof
  obtain ⟨B_idx, M, cc, hcc_eq, φ, hinj, hsurj, hadj, hthin⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA
  intro F C hFC hC
  have hFC' : cc.toSimplicialComplex.IsFacet F C := hcc_eq ▸ hFC
  have hC' : cc.toSimplicialComplex.IsMaximal C := hcc_eq ▸ hC
  obtain ⟨D, ⟨hDne, hFD, hDmax⟩, huniq⟩ := hthin F C hFC' hC'
  refine ⟨D, ⟨hDne, hcc_eq ▸ hFD, hcc_eq ▸ hDmax⟩, ?_⟩
  intro D' ⟨hD'ne, hFD', hD'max⟩
  apply huniq
  exact ⟨hD'ne, hcc_eq ▸ hFD', hcc_eq ▸ hD'max⟩


private lemma apt_facet_of_maximal_containing
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C D F₀ : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC_max : A.IsMaximal C)
  (hD_max : A.IsMaximal D)
  (hF₀_C : A.IsFacet F₀ C)
  (hF₀_sub_D : F₀ ⊆ D) :
-- imply
  A.IsFacet F₀ D := by
-- proof
  obtain ⟨B_idx, M, cc, hcc_eq, φ, hinj, hsurj, hadj, _⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA
  subst hcc_eq
  obtain ⟨g, hg⟩ := cc.gallery_connected C D hC_max hD_max
  have hcard_eq : C.card = D.card := card_eq_of_gallery g hg
  have hF₀_face : F₀ ∈ cc.toSimplicialComplex.faces := hF₀_C.1.1
  have hF₀_sub_C : F₀ ⊆ C := hF₀_C.1.2.2
  have hC_diff : (C \ F₀).card = 1 := hF₀_C.2
  have hD_diff : (D \ F₀).card = 1 := by
    have h1 := Finset.card_sdiff_add_card_inter C F₀
    have h2 := Finset.card_sdiff_add_card_inter D F₀
    rw [Finset.inter_eq_right.mpr hF₀_sub_C] at h1
    rw [Finset.inter_eq_right.mpr hF₀_sub_D] at h2
    omega
  exact ⟨⟨hF₀_face, hD_max.1, hF₀_sub_D⟩, hD_diff⟩


private lemma thin_unique_other_chamber
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {F C D₁ D₂ : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC_max : A.IsMaximal C)
  (hF_C : A.IsFacet F C)
  (hD₁_max : A.IsMaximal D₁)
  (hD₁_ne : D₁ ≠ C)
  (hF_D₁ : A.IsFacet F D₁)
  (hD₂_max : A.IsMaximal D₂)
  (hD₂_ne : D₂ ≠ C)
  (hF_D₂ : A.IsFacet F D₂) :
-- imply
  D₁ = D₂ :=
-- proof
  ExistsUnique.unique (apt_is_thin b A hA F C hF_C hC_max)
    ⟨hD₁_ne, hF_D₁, hD₁_max⟩ ⟨hD₂_ne, hF_D₂, hD₂_max⟩


private lemma apt_chamber_with_facet_is_C_or_C'
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C C' D F₀ : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC_max : A.IsMaximal C)
  (hC'_max : A.IsMaximal C')
  (hD_max : A.IsMaximal D)
  (hne : C ≠ C')
  (hF₀_C : A.IsFacet F₀ C)
  (hF₀_C' : A.IsFacet F₀ C')
  (hF₀_sub_D : F₀ ⊆ D) :
-- imply
  D = C ∨ D = C' := by
-- proof
  by_cases hD_eq_C : D = C
  · left; exact hD_eq_C
  · right
    have hF₀_D := apt_facet_of_maximal_containing b A hA hC_max hD_max hF₀_C hF₀_sub_D
    exact (thin_unique_other_chamber hA hC_max hF₀_C hC'_max hne.symm hF₀_C'
      hD_max hD_eq_C hF₀_D).symm


private lemma card_eq_of_adjacent_eq
  {V : Type}
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C D : Finset V}
-- given
  (hadj : K.Adjacent C D) :
-- imply
  C.card = D.card := by
-- proof
  apply AptFoldingFromRetraction.card_eq_of_adjacent hadj

private lemma list_chain_preserves_eq
  {V : Type}
  [DecidableEq V]
  {R : α → α → Prop}
  {f : α → ℕ}
-- given
  (hR : ∀ a b, R a b → f a = f b) :
-- imply
  ∀ (l : List α) (hl : l ≠ []) (_ : List.IsChain R l), f (l.head hl) = f (l.getLast hl) := by
-- proof
  apply AptFoldingFromRetraction.list_chain_preserves hR

private lemma card_eq_of_gallery_eq
  {V : Type}
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C D : Finset V}
  {g : Gallery K}
-- given
  (hconn : g.Connects C D) :
-- imply
  C.card = D.card := by
-- proof
  apply AptFoldingFromRetraction.card_eq_of_gallery g hconn

private lemma retraction_fixes_face_eq
  {V : Type}
  [DecidableEq V]
  {A : SimplicialComplex V}
  {ρ : V → V}
  {s : Finset V}
-- given
  (hρ_fix : ∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ v = v)
  (hs : s ∈ A.faces) :
-- imply
  s.image ρ = s := by
-- proof
  apply AptFoldingFromRetraction.retraction_fixes_face hρ_fix hs

private lemma third_chamber_from_thickness_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {C C' : Finset V}
-- given
  (hthick : K.IsThick)
  (hadj : K.toSimplicialComplex.Adjacent C C') :
-- imply
  ∃ E F, E ≠ C ∧ E ≠ C' ∧ K.toSimplicialComplex.IsMaximal E ∧ K.toSimplicialComplex.IsFacet F C ∧ K.toSimplicialComplex.IsFacet F C' ∧ K.toSimplicialComplex.IsFacet F E := by
-- proof
  apply AptFoldingFromRetraction.third_chamber_from_thickness hthick hadj


-- created on 2026-10-24
