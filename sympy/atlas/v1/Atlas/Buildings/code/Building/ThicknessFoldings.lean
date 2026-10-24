/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Lemma.Finset.Any_And_All_EqAndAll_IsMaximalAndAll_EqImageSOrAdjacentAndAll_Eq.of.IsMaximal.In_Apartments
import Lemma.Finset.Any_And_Subset.of.In_Faces.In_Apartments
import sympy.atlas.v1.Atlas.Buildings.code.Building.AptThinness

open scoped Classical
open ChamberComplex AptIsCoxeterProof

variable {V : Type} [DecidableEq V]

/-- Boundary-crossing principle: in a chain whose head satisfies $P$ but
some entry does not, there exists an $R$-related adjacent pair witnessing
the transition from $P$ to $\neg P$. -/
theorem chain_transition {α : Type*} (R : α → α → Prop) (P : α → Prop)
    (l : List α) (hchain : List.IsChain R l)
    (hl : l ≠ [])
    (hhead : P (l.head hl))
    (hE : ∃ e ∈ l, ¬P e) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ R a b ∧ P a ∧ ¬P b := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    cases xs with
    | nil =>
      obtain ⟨e, he_mem, he_not⟩ := hE
      simp at he_mem
      subst he_mem
      exact absurd hhead he_not
    | cons y ys =>
      simp only [List.head_cons] at hhead
      by_cases hy : P y
      · have hchain' : List.IsChain R (y :: ys) := List.IsChain.tail hchain
        have hne' : (y :: ys) ≠ [] := List.cons_ne_nil _ _
        obtain ⟨e, he_mem, he_not⟩ := hE
        simp at he_mem
        rcases he_mem with rfl | rfl | he_ys
        · exact absurd hhead he_not
        · exact absurd hy he_not
        · have hE' : ∃ e ∈ (y :: ys), ¬P e := ⟨e, List.mem_cons_of_mem _ he_ys, he_not⟩
          obtain ⟨a, b, ha, hb, hab, hPa, hPb⟩ := ih hchain' hne' hy hE'
          exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hab, hPa, hPb⟩
      · have hRxy : R x y := List.IsChain.rel_head hchain
        exact ⟨x, y, List.mem_cons_self, by simp, hRxy, hhead, hy⟩

namespace ThicknessFoldings

/-- Every apartment is thin: each facet $F \subset C$ lies in exactly one
other chamber $D$ of the apartment. -/
theorem apt_is_thin_pre (K : ChamberComplex V)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ∀ F C, A.IsFacet F C → A.IsMaximal C →
      ∃! D, D ≠ C ∧ A.IsFacet F D ∧ A.IsMaximal D := by
  obtain ⟨cc, hcc_eq, hcc_thin⟩ := pre.apt_thin_cc A hA
  intro F C hFC hC
  have hFC' : cc.toSimplicialComplex.IsFacet F C := hcc_eq ▸ hFC
  have hC' : cc.toSimplicialComplex.IsMaximal C := hcc_eq ▸ hC
  obtain ⟨D, ⟨hDne, hFD, hDmax⟩, huniq⟩ := hcc_thin F C hFC' hC'
  refine ⟨D, ⟨hDne, hcc_eq ▸ hFD, hcc_eq ▸ hDmax⟩, ?_⟩
  intro D' ⟨hD'ne, hFD', hD'max⟩
  apply huniq
  exact ⟨hD'ne, hcc_eq ▸ hFD', hcc_eq ▸ hD'max⟩

/-- Chamber transitivity for the pre-apartment system: for any two chambers
$C, D$ of an apartment, there is a bijective vertex map sending $C$ to $D$. -/
theorem apt_automorphism_sending_chamber_pre
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (D : Finset V) (hD : A.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C :=
  pre.apt_automorphism A hA C hC D hD

/-- A bijective vertex map fixing a chamber pointwise is the identity on the
apartment (pre-apartment version). -/
theorem bij_iso_fixing_chamber_is_id_pre
    (pre : PreApartmentData K)
    (B B' : SimplicialComplex V) (hB : B ∈ pre.apartments)
    (D : Finset V) (hD_B : D ∈ B.faces)
    (hD_max : K.toSimplicialComplex.IsMaximal D)
    (φ : V → V) (hφ_bij : Function.Bijective φ)
    (_hφ_faces : ∀ s, s ∈ B.faces ↔ s.image φ ∈ B'.faces)
    (hφ_D : D.image φ = D) :
    ∀ s ∈ B.faces, s.image φ = s := by
  have hD_max_B : B.IsMaximal D :=
    pre.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max
  have hmono_id : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t → s ⊂ t :=
    fun _ _ _ _ h => h
  have hmono_φ : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t →
      s.image φ ⊂ t.image φ :=
    fun _ _ _ _ hst => finset_image_ssubset_of_injective hφ_bij.1 hst
  obtain ⟨_, hprop⟩ := pre.apt_unique_labelling B hB
    V V id (fun s => s.image φ) hmono_id hmono_φ D hD_max_B
  have h_agree_D : D.image φ = (id D).image (id : V → V) := by
    simp [hφ_D]
  intro s hs
  have := hprop id Function.bijective_id h_agree_D s hs
  simp at this
  exact this

/-- Any apartment iso fixing a chamber is bijective (pre-apartment version). -/
theorem iso_bijective_fixing_chamber_pre
    (pre : PreApartmentData K)
    (B : SimplicialComplex V) (hB : B ∈ pre.apartments)
    (B₀ : SimplicialComplex V) (hB₀ : B₀ ∈ pre.apartments)
    (D : Finset V) (hD_B : D ∈ B.faces) (hD_B₀ : D ∈ B₀.faces)
    (hD_max_B : B.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ B.faces ↔ s.image φ ∈ B₀.faces) ∧
      D.image φ = D := by
  obtain ⟨ψ, hψ_bij, hψ_faces⟩ :=
    pre.iso_bijective B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B
  have hDψ_max_B₀ : B₀.IsMaximal (D.image ψ) :=
    bijective_face_iso_preserves_maximal hψ_bij hψ_faces hD_max_B
  have hD_max_B₀ : B₀.IsMaximal D :=
    pre.building_maximal_in_apt_is_apt_maximal B₀ hB₀ D hD_B₀
      (pre.maximal_in_apt_is_maximal B hB D hD_max_B)
  obtain ⟨α, hα_bij, hα_faces, hα_send⟩ :=
    apt_automorphism_sending_chamber_pre pre B₀ hB₀ D hD_max_B₀ (D.image ψ) hDψ_max_B₀
  refine ⟨α ∘ ψ, hα_bij.comp hψ_bij, ?_, ?_⟩
  · intro s
    simp only [← Finset.image_image]
    exact Iff.trans (hψ_faces s) (hα_faces (s.image ψ))
  · simp only [← Finset.image_image]
    exact hα_send

/-- Existence of the canonical retraction $\rho_{D;C,A}$ for a
pre-apartment system. -/
theorem exists_canonical_retraction_pre (K : ChamberComplex V)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (C : Finset V) (hC : A.IsMaximal C) :
    ∃ (ρ : V → V),
      (∀ s ∈ K.toSimplicialComplex.faces, s.image ρ ∈ A.faces) ∧
      (∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ v = v) ∧
      (∀ D, K.toSimplicialComplex.IsMaximal D →
            A.IsMaximal (D.image ρ)) ∧
      (∀ D₁ D₂, K.toSimplicialComplex.Adjacent D₁ D₂ →
        D₁.image ρ = D₂.image ρ ∨ A.Adjacent (D₁.image ρ) (D₂.image ρ)) ∧
      (∀ (B : SimplicialComplex V), B ∈ pre.apartments →
        C ∈ B.faces →
        ∀ v₁ v₂, (∃ s ∈ B.faces, v₁ ∈ s) → (∃ s ∈ B.faces, v₂ ∈ s) →
          ρ v₁ = ρ v₂ → v₁ = v₂) ∧

      (∀ v, ∃ s ∈ A.faces, ρ v ∈ s) ∧


      (∀ (B : SimplicialComplex V), B ∈ pre.apartments →
        C ∈ B.faces →
        ∀ (σ : V → V),
          (∀ s ∈ K.toSimplicialComplex.faces, s.image σ ∈ B.faces) →
          (∀ v, (∃ s ∈ B.faces, v ∈ s) → σ v = v) →
          ∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ (σ v) = v) := by
  have hC_K := pre.maximal_in_apt_is_maximal A hA C hC

  have apt_faces_sub : ∀ (B : SimplicialComplex V), B ∈ pre.apartments →
      C ∈ B.faces → B.faces ⊆ A.faces := by
    intro B hB hC_B s hs
    have hC_max_B : B.IsMaximal C :=
      pre.building_maximal_in_apt_is_apt_maximal B hB C hC_B hC_K
    obtain ⟨φ, hφ_bij, hφ_faces, hφ_C⟩ :=
      iso_bijective_fixing_chamber_pre pre B hB A hA C hC_B hC.1 hC_max_B
    have hid := bij_iso_fixing_chamber_is_id_pre pre B A hB C hC_B hC_K
      φ hφ_bij hφ_faces hφ_C s hs
    rw [← hid]
    exact (hφ_faces s).mp hs

  have apt_faces_sup : ∀ (B : SimplicialComplex V), B ∈ pre.apartments →
      C ∈ B.faces → A.faces ⊆ B.faces := by
    intro B hB hC_B s hs
    have hC_max_B : B.IsMaximal C :=
      pre.building_maximal_in_apt_is_apt_maximal B hB C hC_B hC_K
    obtain ⟨ψ, hψ_bij, hψ_faces, hψ_C⟩ :=
      iso_bijective_fixing_chamber_pre pre A hA B hB C hC.1 hC_B hC
    have hid := bij_iso_fixing_chamber_is_id_pre pre A B hA C hC.1 hC_K
      ψ hψ_bij hψ_faces hψ_C s hs
    rw [← hid]
    exact (hψ_faces s).mp hs

  have all_faces_in_A : ∀ s ∈ K.toSimplicialComplex.faces, s ∈ A.faces := by
    intro s hs
    obtain ⟨E, hE_max, hs_sub⟩ := K.exists_maximal s hs
    obtain ⟨B, hB, hC_B, hE_B⟩ := pre.contains_pair C E hC_K hE_max
    have hs_B : s ∈ B.faces :=
      B.down_closed hE_B hs_sub (K.toSimplicialComplex.nonempty_of_mem s hs)
    exact apt_faces_sub B hB hC_B hs_B

  have hC_ne : C.Nonempty := K.toSimplicialComplex.nonempty_of_mem C (pre.sub A hA hC.1)
  obtain ⟨v₀, hv₀⟩ := hC_ne

  let ρ : V → V := fun v =>
    if ∃ s ∈ K.toSimplicialComplex.faces, v ∈ s then v else v₀

  have hρ_id : ∀ v, (∃ s ∈ K.toSimplicialComplex.faces, v ∈ s) → ρ v = v := by
    intro v hv
    show (if ∃ s ∈ K.toSimplicialComplex.faces, v ∈ s then v else v₀) = v
    rw [if_pos hv]

  have hρ_junk : ∀ v, ¬(∃ s ∈ K.toSimplicialComplex.faces, v ∈ s) → ρ v = v₀ := by
    intro v hv
    show (if ∃ s ∈ K.toSimplicialComplex.faces, v ∈ s then v else v₀) = v₀
    rw [if_neg hv]

  have hρ_image_eq : ∀ s ∈ K.toSimplicialComplex.faces, s.image ρ = s := by
    intro s hs
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hρ_id w ⟨s, hs, hw⟩]
      exact hw
    · intro hv
      exact ⟨v, hv, hρ_id v ⟨s, hs, hv⟩⟩

  refine ⟨ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s hs
    rw [hρ_image_eq s hs]
    exact all_faces_in_A s hs
  ·
    intro v ⟨s, hs, hvs⟩
    exact hρ_id v ⟨s, pre.sub A hA hs, hvs⟩
  ·
    intro D hD_max
    rw [hρ_image_eq D hD_max.1]
    exact pre.building_maximal_in_apt_is_apt_maximal A hA D (all_faces_in_A D hD_max.1) hD_max
  ·
    intro D₁ D₂ hadj
    rw [hρ_image_eq D₁ hadj.1.1, hρ_image_eq D₂ hadj.2.1.1]
    obtain ⟨hD₁_max, hD₂_max, hne, F, hF₁, hF₂⟩ := hadj
    by_cases heq : D₁ = D₂
    · left; exact heq
    · right
      exact ⟨pre.building_maximal_in_apt_is_apt_maximal A hA D₁ (all_faces_in_A D₁ hD₁_max.1) hD₁_max,
              pre.building_maximal_in_apt_is_apt_maximal A hA D₂ (all_faces_in_A D₂ hD₂_max.1) hD₂_max,
              hne, F,
              ⟨⟨A.down_closed (all_faces_in_A D₁ hD₁_max.1) hF₁.1.2.2
                  (K.toSimplicialComplex.nonempty_of_mem F hF₁.1.1),
                all_faces_in_A D₁ hD₁_max.1, hF₁.1.2.2⟩,
               hF₁.2⟩,
              ⟨⟨A.down_closed (all_faces_in_A D₂ hD₂_max.1) hF₂.1.2.2
                  (K.toSimplicialComplex.nonempty_of_mem F hF₂.1.1),
                all_faces_in_A D₂ hD₂_max.1, hF₂.1.2.2⟩,
               hF₂.2⟩⟩
  ·
    intro B hB hC_B v₁ v₂ hv₁ hv₂ h

    obtain ⟨s₁, hs₁, hv₁s⟩ := hv₁
    obtain ⟨s₂, hs₂, hv₂s⟩ := hv₂
    rw [hρ_id v₁ ⟨s₁, pre.sub B hB hs₁, hv₁s⟩,
        hρ_id v₂ ⟨s₂, pre.sub B hB hs₂, hv₂s⟩] at h
    exact h
  ·
    intro v
    by_cases hv : ∃ s ∈ K.toSimplicialComplex.faces, v ∈ s
    · obtain ⟨s, hs, hvs⟩ := hv
      exact ⟨s, all_faces_in_A s hs, by rw [hρ_id v ⟨s, hs, hvs⟩]; exact hvs⟩
    ·
      exact ⟨C, hC.1, by rw [hρ_junk v hv]; exact hv₀⟩
  ·
    intro B hB hC_B σ _hσ_simp hσ_fix v hv

    obtain ⟨s, hs, hvs⟩ := hv
    have hσv : σ v = v := hσ_fix v ⟨s, apt_faces_sup B hB hC_B hs, hvs⟩

    rw [hσv, hρ_id v ⟨s, pre.sub A hA hs, hvs⟩]

/-- A facet $F$ contained in a maximal chamber $C$ of an apartment is a
facet of $C$ in the apartment. -/
theorem apt_facet_of_maximal_containing_pre
    (K : ChamberComplex V)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    {C D F₀ : Finset V}
    (hC_max : A.IsMaximal C) (hD_max : A.IsMaximal D)
    (hF₀_C : A.IsFacet F₀ C) (hF₀_sub_D : F₀ ⊆ D) :
    A.IsFacet F₀ D := by
  obtain ⟨cc, hcc_eq, _hcc_thin⟩ := pre.apt_thin_cc A hA
  subst hcc_eq
  obtain ⟨g, hg⟩ := cc.gallery_connected C D hC_max hD_max
  have hcard_eq : C.card = D.card :=
    AptFoldingFromRetraction.card_eq_of_gallery g hg
  have hF₀_sub_C : F₀ ⊆ C := hF₀_C.1.2.2
  have hC_diff : (C \ F₀).card = 1 := hF₀_C.2
  have hD_diff : (D \ F₀).card = 1 := by
    have h1 := Finset.card_sdiff_add_card_inter C F₀
    have h2 := Finset.card_sdiff_add_card_inter D F₀
    rw [Finset.inter_eq_right.mpr hF₀_sub_C] at h1
    rw [Finset.inter_eq_right.mpr hF₀_sub_D] at h2
    omega
  exact ⟨⟨hF₀_C.1.1, hD_max.1, hF₀_sub_D⟩, hD_diff⟩

/-- Pre-apartment thinness: each facet $F$ has a unique other chamber $D$
besides $C$ in the apartment. -/
theorem thin_unique_other_chamber_pre
    (K : ChamberComplex V)
    (pre : PreApartmentData K)
    {A : SimplicialComplex V} (hA : A ∈ pre.apartments)
    {F C D₁ D₂ : Finset V}
    (hC_max : A.IsMaximal C)
    (hF_C : A.IsFacet F C)
    (hD₁_max : A.IsMaximal D₁) (hD₁_ne : D₁ ≠ C) (hF_D₁ : A.IsFacet F D₁)
    (hD₂_max : A.IsMaximal D₂) (hD₂_ne : D₂ ≠ C) (hF_D₂ : A.IsFacet F D₂) :
    D₁ = D₂ :=
  ExistsUnique.unique (apt_is_thin_pre K pre A hA F C hF_C hC_max)
    ⟨hD₁_ne, hF_D₁, hD₁_max⟩ ⟨hD₂_ne, hF_D₂, hD₂_max⟩

/-- A chamber of the apartment containing a facet $F$ is either $C$ or its
unique opposite chamber across $F$. -/
theorem apt_chamber_with_facet_is_C_or_C_pre
    (K : ChamberComplex V)
    (pre : PreApartmentData K)
    {A : SimplicialComplex V} (hA : A ∈ pre.apartments)
    {C C' D F₀ : Finset V}
    (hC_max : A.IsMaximal C) (hC'_max : A.IsMaximal C')
    (hD_max : A.IsMaximal D)
    (hne : C ≠ C')
    (hF₀_C : A.IsFacet F₀ C) (hF₀_C' : A.IsFacet F₀ C')
    (hF₀_sub_D : F₀ ⊆ D) :
    D = C ∨ D = C' := by
  by_cases hD_eq_C : D = C
  · left; exact hD_eq_C
  · right
    have hF₀_D := apt_facet_of_maximal_containing_pre K pre A hA hC_max hD_max hF₀_C hF₀_sub_D
    exact (thin_unique_other_chamber_pre K pre hA hC_max hF₀_C hC'_max hne.symm hF₀_C'
      hD_max hD_eq_C hF₀_D).symm

/-- For adjacent chambers $C, C'$, there is a vertex map fixing $C$ and
sending the third chamber containing the panel to $C'$ (used to construct
foldings from thickness). -/
theorem exists_map_fixing_sending_adj_pre
    (K : ChamberComplex V) (hK_thick : K.IsThick)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (C C' : Finset V)
    (hC_A : A.IsMaximal C) (hC'_A : A.IsMaximal C')
    (hadj_A : A.Adjacent C C') :
    ∃ f : V → V,
      C.image f = C ∧
      C'.image f = C ∧
      (∀ s ∈ A.faces, s.image f ∈ A.faces) ∧
      (∀ v, f (f v) = f v) ∧
      (∀ D, A.IsMaximal D → A.IsMaximal (D.image f)) ∧
      (∀ F D, A.IsFacet F D → A.IsFacet (F.image f) (D.image f)) ∧

      (∀ (cc : ChamberComplex V), cc.toSimplicialComplex = A →
        ∀ D, cc.toSimplicialComplex.IsMaximal D →
        D.image f = D →
        ∃! D', cc.toSimplicialComplex.IsMaximal D' ∧ D' ≠ D ∧ D'.image f = D) ∧

      (∀ (cc : ChamberComplex V), cc.toSimplicialComplex = A →
        ∀ (A₀ B : Finset V),
        cc.toSimplicialComplex.IsMaximal A₀ → A₀.image f = A₀ →
        cc.toSimplicialComplex.IsMaximal B → B.image f = B →
        ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A₀ B →
        g.length = galleryDist cc.toSimplicialComplex A₀ B →
        ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers →
          cc.toSimplicialComplex.Adjacent Ci Ci1 →
          Ci1.image f = Ci.image f → False) := by

  have hC_K := pre.maximal_in_apt_is_maximal A hA C hC_A
  have hC'_K := pre.maximal_in_apt_is_maximal A hA C' hC'_A
  have hA_sub := pre.sub A hA
  obtain ⟨_, _, hne, F, hF_C_A, hF_C'_A⟩ := hadj_A

  have hF_K_C : K.toSimplicialComplex.IsFacet F C :=
    ⟨⟨hA_sub hF_C_A.1.1, hA_sub hC_A.1, hF_C_A.1.2.2⟩, hF_C_A.2⟩
  have hF_K_C' : K.toSimplicialComplex.IsFacet F C' :=
    ⟨⟨hA_sub hF_C'_A.1.1, hA_sub hC'_A.1, hF_C'_A.1.2.2⟩, hF_C'_A.2⟩
  have hadj_K : K.toSimplicialComplex.Adjacent C C' :=
    ⟨hC_K, hC'_K, hne, F, hF_K_C, hF_K_C'⟩

  obtain ⟨E, F₀, hE_ne_C, hE_ne_C', hE_K_max, hF₀_K_C, hF₀_K_C', hF₀_K_E⟩ :=
    AptFoldingFromRetraction.third_chamber_from_thickness hK_thick hadj_K

  obtain ⟨A', hA', hC_A', hE_A'⟩ :=
    pre.contains_pair C E hC_K hE_K_max
  have hA'_sub := pre.sub A' hA'
  have hC_A'_max := pre.building_maximal_in_apt_is_apt_maximal
    A' hA' C hC_A' hC_K

  obtain ⟨ρ₁, hρ₁_face, hρ₁_fix, hρ₁_ch, hρ₁_adj, hρ₁_inj, hρ₁_img, hρ₁_rt⟩ :=
    exists_canonical_retraction_pre K pre A' hA' C hC_A'_max
  obtain ⟨ρ₂, hρ₂_face, hρ₂_fix, hρ₂_ch, hρ₂_adj, hρ₂_inj, hρ₂_img, hρ₂_rt⟩ :=
    exists_canonical_retraction_pre K pre A hA C' hC'_A

  have hF₀_A' : F₀ ∈ A'.faces :=
    A'.down_closed hC_A' hF₀_K_C.1.2.2
      (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1)
  have hF₀_A : F₀ ∈ A.faces :=
    A.down_closed hC_A.1 hF₀_K_C.1.2.2
      (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1)
  have hF₀_C_A : A.IsFacet F₀ C :=
    ⟨⟨hF₀_A, hC_A.1, hF₀_K_C.1.2.2⟩, hF₀_K_C.2⟩
  have hF₀_sub_C' : F₀ ⊆ C' := hF₀_K_C'.1.2.2
  have hF₀_C'_A : A.IsFacet F₀ C' :=
    ⟨⟨hF₀_A, hC'_A.1, hF₀_sub_C'⟩, hF₀_K_C'.2⟩

  refine ⟨ρ₂ ∘ ρ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · rw [show C.image (ρ₂ ∘ ρ₁) = (C.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]
    rw [AptFoldingFromRetraction.retraction_fixes_face hρ₁_fix hC_A',
        AptFoldingFromRetraction.retraction_fixes_face hρ₂_fix hC_A.1]

  · rw [show C'.image (ρ₂ ∘ ρ₁) = (C'.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]

    have hC_ρ₁ : C.image ρ₁ = C :=
      AptFoldingFromRetraction.retraction_fixes_face hρ₁_fix hC_A'

    have h_cases := hρ₁_adj C C' hadj_K
    rw [hC_ρ₁] at h_cases
    cases h_cases with
    | inl h_eq =>

      rw [← h_eq, AptFoldingFromRetraction.retraction_fixes_face hρ₂_fix hC_A.1]
    | inr h_adj_A' =>


      have hF₀_sub_ρ₁C' : F₀ ⊆ C'.image ρ₁ := by
        intro v hv
        rw [Finset.mem_image]
        exact ⟨v, hF₀_sub_C' hv, hρ₁_fix v ⟨F₀, hF₀_A', hv⟩⟩

      have hF₀_sub_ρ₂ρ₁C' : F₀ ⊆ (C'.image ρ₁).image ρ₂ := by
        intro v hv
        rw [Finset.mem_image]
        exact ⟨v, hF₀_sub_ρ₁C' hv, hρ₂_fix v ⟨F₀, hF₀_A, hv⟩⟩

      have hρ₁C'_A'_max : A'.IsMaximal (C'.image ρ₁) := hρ₁_ch C' hC'_K
      have hρ₁C'_K : K.toSimplicialComplex.IsMaximal (C'.image ρ₁) :=
        pre.maximal_in_apt_is_maximal A' hA' (C'.image ρ₁) hρ₁C'_A'_max

      have hρ₂ρ₁C'_A_max : A.IsMaximal ((C'.image ρ₁).image ρ₂) :=
        hρ₂_ch (C'.image ρ₁) hρ₁C'_K


      obtain ⟨B, hB, hρ₁C'_B, hC'_B⟩ :=
        pre.contains_pair (C'.image ρ₁) C' hρ₁C'_K hC'_K
      have h_ne_C' : (C'.image ρ₁).image ρ₂ ≠ C' := by
        intro h_eq_C'

        have h_sub : C'.image ρ₁ ⊆ C' := by
          intro v hv
          rw [Finset.mem_image] at hv
          obtain ⟨w, hw, rfl⟩ := hv
          have hρ₂_ρ₁w : ρ₂ (ρ₁ w) ∈ C' := by
            rw [← h_eq_C']
            exact Finset.mem_image_of_mem ρ₂ (Finset.mem_image_of_mem ρ₁ hw)
          have hρ₁w_in_B : ∃ s ∈ B.faces, ρ₁ w ∈ s :=
            ⟨C'.image ρ₁, hρ₁C'_B, Finset.mem_image_of_mem ρ₁ hw⟩
          have hu_in_B : ∃ s ∈ B.faces, (ρ₂ (ρ₁ w)) ∈ s :=
            ⟨C', hC'_B, hρ₂_ρ₁w⟩
          have : ρ₁ w = ρ₂ (ρ₁ w) :=
            hρ₂_inj B hB hC'_B (ρ₁ w) (ρ₂ (ρ₁ w)) hρ₁w_in_B hu_in_B
              (hρ₂_fix (ρ₂ (ρ₁ w)) ⟨C', hC'_A.1, hρ₂_ρ₁w⟩).symm
          rw [this]; exact hρ₂_ρ₁w
        have h_ρ₁C'_eq_C' : C'.image ρ₁ = C' := hρ₁C'_K.2 C' hC'_K.1 h_sub
        exfalso
        have hC'_A'_max : A'.IsMaximal C' := by
          rw [← h_ρ₁C'_eq_C']; exact hρ₁C'_A'_max
        have hE_A'_max : A'.IsMaximal E :=
          pre.building_maximal_in_apt_is_apt_maximal A' hA' E hE_A' hE_K_max
        have hF₀_C_A' : A'.IsFacet F₀ C :=
          ⟨⟨hF₀_A', hC_A'_max.1, hF₀_K_C.1.2.2⟩, hF₀_K_C.2⟩
        have hC'_A'_face : C' ∈ A'.faces := hC'_A'_max.1
        have hF₀_C'_A' : A'.IsFacet F₀ C' :=
          ⟨⟨A'.down_closed hC'_A'_face hF₀_sub_C'
              (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1),
            hC'_A'_face, hF₀_sub_C'⟩, hF₀_K_C'.2⟩
        have hF₀_E_A' : A'.IsFacet F₀ E :=
          ⟨⟨A'.down_closed hE_A' hF₀_K_E.1.2.2
              (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1),
            hE_A', hF₀_K_E.1.2.2⟩, hF₀_K_E.2⟩

        exact hE_ne_C' (thin_unique_other_chamber_pre K pre hA' hC_A'_max hF₀_C_A'
          hC'_A'_max hne.symm hF₀_C'_A' hE_A'_max hE_ne_C hF₀_E_A').symm


      have h_C_or_C' := apt_chamber_with_facet_is_C_or_C_pre K pre hA hC_A hC'_A
        hρ₂ρ₁C'_A_max hne hF₀_C_A hF₀_C'_A hF₀_sub_ρ₂ρ₁C'
      cases h_C_or_C' with
      | inl h_eq_C => exact h_eq_C
      | inr h_eq_C' => exact absurd h_eq_C' h_ne_C'

  · intro s hs
    rw [show s.image (ρ₂ ∘ ρ₁) = (s.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]
    have hA'_sub' := pre.sub A' hA'
    exact hρ₂_face (s.image ρ₁) (hA'_sub' (hρ₁_face s (hA_sub hs)))

  · intro v


    show ρ₂ (ρ₁ (ρ₂ (ρ₁ v))) = ρ₂ (ρ₁ v)


    have hw_A' : ∃ s ∈ A'.faces, ρ₁ v ∈ s := hρ₁_img v
    have hC_A_face : C ∈ A.faces := hC_A.1
    have hρ₁_ρ₂_w : ρ₁ (ρ₂ (ρ₁ v)) = ρ₁ v :=
      hρ₁_rt A hA hC_A_face ρ₂ hρ₂_face hρ₂_fix (ρ₁ v) hw_A'

    exact congrArg ρ₂ hρ₁_ρ₂_w

  · intro D hD

    have hD_K := pre.maximal_in_apt_is_maximal A hA D hD
    rw [show D.image (ρ₂ ∘ ρ₁) = (D.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]
    have hρ₁D_A'_max : A'.IsMaximal (D.image ρ₁) := hρ₁_ch D hD_K
    have hρ₁D_K : K.toSimplicialComplex.IsMaximal (D.image ρ₁) :=
      pre.maximal_in_apt_is_maximal A' hA' (D.image ρ₁) hρ₁D_A'_max
    exact hρ₂_ch (D.image ρ₁) hρ₁D_K

  · intro F_arg D_arg hfacet
    rw [show F_arg.image (ρ₂ ∘ ρ₁) = (F_arg.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]
    rw [show D_arg.image (ρ₂ ∘ ρ₁) = (D_arg.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]
    have hF_face : F_arg ∈ A.faces := hfacet.1.1
    have hD_face : D_arg ∈ A.faces := hfacet.1.2.1
    have hF_sub_D : F_arg ⊆ D_arg := hfacet.1.2.2
    have hsdiff : (D_arg \ F_arg).card = 1 := hfacet.2

    have hρ₁_injA : ∀ v₁ v₂, (∃ s ∈ A.faces, v₁ ∈ s) → (∃ s ∈ A.faces, v₂ ∈ s) →
        ρ₁ v₁ = ρ₁ v₂ → v₁ = v₂ := hρ₁_inj A hA hC_A.1
    have hρ₁_injOn_D : Set.InjOn ρ₁ ↑D_arg := by
      intro a ha b hb hab
      exact hρ₁_injA a b ⟨D_arg, hD_face, Finset.mem_coe.mp ha⟩
        ⟨D_arg, hD_face, Finset.mem_coe.mp hb⟩ hab

    have hρ₁D_A' : D_arg.image ρ₁ ∈ A'.faces := hρ₁_face D_arg (hA_sub hD_face)

    obtain ⟨M', hM'_max, hM'_sup⟩ := apt_face_in_chamber pre A' hA' (D_arg.image ρ₁) hρ₁D_A'
    have hM'_K := pre.maximal_in_apt_is_maximal A' hA' M' hM'_max

    obtain ⟨B, hB, hM'_B, hC'_B⟩ := pre.contains_pair M' C' hM'_K hC'_K

    have hρ₂_injB := hρ₂_inj B hB hC'_B
    have hρ₂_injOn_ρ₁D : Set.InjOn ρ₂ ↑(D_arg.image ρ₁) := by
      intro a ha b hb hab
      exact hρ₂_injB a b ⟨M', hM'_B, hM'_sup (Finset.mem_coe.mp ha)⟩
        ⟨M', hM'_B, hM'_sup (Finset.mem_coe.mp hb)⟩ hab

    have hρ₁F_A' : F_arg.image ρ₁ ∈ A'.faces := hρ₁_face F_arg (hA_sub hF_face)
    have hρ₁F_sub : F_arg.image ρ₁ ⊆ D_arg.image ρ₁ := Finset.image_subset_image hF_sub_D
    have hρ₂ρ₁F : (F_arg.image ρ₁).image ρ₂ ∈ A.faces :=
      hρ₂_face (F_arg.image ρ₁) (hA'_sub hρ₁F_A')
    have hρ₂ρ₁D : (D_arg.image ρ₁).image ρ₂ ∈ A.faces :=
      hρ₂_face (D_arg.image ρ₁) (hA'_sub hρ₁D_A')
    have hρ₂ρ₁F_sub : (F_arg.image ρ₁).image ρ₂ ⊆ (D_arg.image ρ₁).image ρ₂ :=
      Finset.image_subset_image hρ₁F_sub
    refine ⟨⟨hρ₂ρ₁F, hρ₂ρ₁D, hρ₂ρ₁F_sub⟩, ?_⟩
    rw [← Finset.image_sdiff_of_injOn hρ₂_injOn_ρ₁D hρ₁F_sub]
    rw [← Finset.image_sdiff_of_injOn hρ₁_injOn_D hF_sub_D]
    rw [Finset.card_image_of_injOn (hρ₂_injOn_ρ₁D.mono (by
      intro x hx; simp at hx ⊢
      obtain ⟨y, ⟨hyd, _⟩, rfl⟩ := hx; exact ⟨y, hyd, rfl⟩))]
    rw [Finset.card_image_of_injOn (hρ₁_injOn_D.mono (by
      intro x hx; exact Finset.mem_coe.mpr (Finset.sdiff_subset (Finset.mem_coe.mp hx))))]
    exact hsdiff

  ·


    have hrt_A : ∀ v, (∃ s ∈ A'.faces, v ∈ s) → ρ₁ (ρ₂ v) = v :=
      hρ₁_rt A hA hC_A.1 ρ₂ hρ₂_face hρ₂_fix

    have hρ₁f_eq : ∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ₁ ((ρ₂ ∘ ρ₁) v) = ρ₁ v := by
      intro v hv
      show ρ₁ (ρ₂ (ρ₁ v)) = ρ₁ v
      exact hrt_A (ρ₁ v) (hρ₁_img v)

    have hfv_A : ∀ v, ∃ s ∈ A.faces, (ρ₂ ∘ ρ₁) v ∈ s := by
      intro v; exact hρ₂_img (ρ₁ v)

    have hρ₁_injA : ∀ v₁ v₂, (∃ s ∈ A.faces, v₁ ∈ s) → (∃ s ∈ A.faces, v₂ ∈ s) →
        ρ₁ v₁ = ρ₁ v₂ → v₁ = v₂ := hρ₁_inj A hA hC_A.1

    have hf_id : ∀ v, (∃ s ∈ A.faces, v ∈ s) → (ρ₂ ∘ ρ₁) v = v := by
      intro v hv
      exact (hρ₁_injA v ((ρ₂ ∘ ρ₁) v) hv (hfv_A v) (hρ₁f_eq v hv).symm).symm


    exfalso
    have : C'.image (ρ₂ ∘ ρ₁) = C' := by
      ext v
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have h := hf_id w ⟨C', hC'_A.1, hw⟩
        show (ρ₂ ∘ ρ₁) w ∈ C'
        rw [h]
        exact hw
      · intro hv
        exact ⟨v, hv, hf_id v ⟨C', hC'_A.1, hv⟩⟩


    have hC'_fix : C'.image (ρ₂ ∘ ρ₁) = C' := this

    have hC'_fold : C'.image (ρ₂ ∘ ρ₁) = C := by
      rw [show C'.image (ρ₂ ∘ ρ₁) = (C'.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]
      have hC_ρ₁ : C.image ρ₁ = C :=
        AptFoldingFromRetraction.retraction_fixes_face hρ₁_fix hC_A'
      have h_cases := hρ₁_adj C C' hadj_K
      rw [hC_ρ₁] at h_cases
      cases h_cases with
      | inl h_eq =>
        rw [← h_eq, AptFoldingFromRetraction.retraction_fixes_face hρ₂_fix hC_A.1]
      | inr h_adj_A' =>
        have hF₀_sub_ρ₁C' : F₀ ⊆ C'.image ρ₁ := by
          intro v hv
          rw [Finset.mem_image]
          exact ⟨v, hF₀_sub_C' hv, hρ₁_fix v ⟨F₀, hF₀_A', hv⟩⟩
        have hF₀_sub_ρ₂ρ₁C' : F₀ ⊆ (C'.image ρ₁).image ρ₂ := by
          intro v hv
          rw [Finset.mem_image]
          exact ⟨v, hF₀_sub_ρ₁C' hv, hρ₂_fix v ⟨F₀, hF₀_A, hv⟩⟩
        have hρ₁C'_A'_max : A'.IsMaximal (C'.image ρ₁) := hρ₁_ch C' hC'_K
        have hρ₁C'_K : K.toSimplicialComplex.IsMaximal (C'.image ρ₁) :=
          pre.maximal_in_apt_is_maximal A' hA' (C'.image ρ₁) hρ₁C'_A'_max
        have hρ₂ρ₁C'_A_max : A.IsMaximal ((C'.image ρ₁).image ρ₂) :=
          hρ₂_ch (C'.image ρ₁) hρ₁C'_K
        obtain ⟨B, hB, hρ₁C'_B, hC'_B⟩ :=
          pre.contains_pair (C'.image ρ₁) C' hρ₁C'_K hC'_K
        have h_ne_C' : (C'.image ρ₁).image ρ₂ ≠ C' := by
          intro h_eq_C'
          have h_sub : C'.image ρ₁ ⊆ C' := by
            intro v hv
            rw [Finset.mem_image] at hv
            obtain ⟨w, hw, rfl⟩ := hv
            have hρ₂_ρ₁w : ρ₂ (ρ₁ w) ∈ C' := by
              rw [← h_eq_C']
              exact Finset.mem_image_of_mem ρ₂ (Finset.mem_image_of_mem ρ₁ hw)
            have hρ₁w_in_B : ∃ s ∈ B.faces, ρ₁ w ∈ s :=
              ⟨C'.image ρ₁, hρ₁C'_B, Finset.mem_image_of_mem ρ₁ hw⟩
            have hu_in_B : ∃ s ∈ B.faces, (ρ₂ (ρ₁ w)) ∈ s :=
              ⟨C', hC'_B, hρ₂_ρ₁w⟩
            have : ρ₁ w = ρ₂ (ρ₁ w) :=
              hρ₂_inj B hB hC'_B (ρ₁ w) (ρ₂ (ρ₁ w)) hρ₁w_in_B hu_in_B
                (hρ₂_fix (ρ₂ (ρ₁ w)) ⟨C', hC'_A.1, hρ₂_ρ₁w⟩).symm
            rw [this]; exact hρ₂_ρ₁w
          have h_ρ₁C'_eq_C' : C'.image ρ₁ = C' := hρ₁C'_K.2 C' hC'_K.1 h_sub
          exfalso
          have hC'_A'_max : A'.IsMaximal C' := by
            rw [← h_ρ₁C'_eq_C']; exact hρ₁C'_A'_max
          have hE_A'_max : A'.IsMaximal E :=
            pre.building_maximal_in_apt_is_apt_maximal A' hA' E hE_A' hE_K_max
          have hF₀_C_A' : A'.IsFacet F₀ C :=
            ⟨⟨hF₀_A', hC_A'_max.1, hF₀_K_C.1.2.2⟩, hF₀_K_C.2⟩
          have hC'_A'_face : C' ∈ A'.faces := hC'_A'_max.1
          have hF₀_C'_A' : A'.IsFacet F₀ C' :=
            ⟨⟨A'.down_closed hC'_A'_face hF₀_sub_C'
                (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1),
              hC'_A'_face, hF₀_sub_C'⟩, hF₀_K_C'.2⟩
          have hF₀_E_A' : A'.IsFacet F₀ E :=
            ⟨⟨A'.down_closed hE_A' hF₀_K_E.1.2.2
                (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1),
              hE_A', hF₀_K_E.1.2.2⟩, hF₀_K_E.2⟩
          exact hE_ne_C' (thin_unique_other_chamber_pre K pre hA' hC_A'_max hF₀_C_A'
            hC'_A'_max hne.symm hF₀_C'_A' hE_A'_max hE_ne_C hF₀_E_A').symm
        have h_C_or_C' := apt_chamber_with_facet_is_C_or_C_pre K pre hA hC_A hC'_A
          hρ₂ρ₁C'_A_max hne hF₀_C_A hF₀_C'_A hF₀_sub_ρ₂ρ₁C'
        cases h_C_or_C' with
        | inl h_eq_C => exact h_eq_C
        | inr h_eq_C' => exact absurd h_eq_C' h_ne_C'
    exact hne (hC'_fold ▸ hC'_fix)

  ·
    exfalso
    have hrt_A : ∀ v, (∃ s ∈ A'.faces, v ∈ s) → ρ₁ (ρ₂ v) = v :=
      hρ₁_rt A hA hC_A.1 ρ₂ hρ₂_face hρ₂_fix
    have hρ₁_injA : ∀ v₁ v₂, (∃ s ∈ A.faces, v₁ ∈ s) → (∃ s ∈ A.faces, v₂ ∈ s) →
        ρ₁ v₁ = ρ₁ v₂ → v₁ = v₂ := hρ₁_inj A hA hC_A.1
    have hf_id : ∀ v, (∃ s ∈ A.faces, v ∈ s) → (ρ₂ ∘ ρ₁) v = v := by
      intro v hv
      exact (hρ₁_injA v ((ρ₂ ∘ ρ₁) v) hv (hρ₂_img (ρ₁ v))
        (hrt_A (ρ₁ v) (hρ₁_img v)).symm).symm
    have hf_id' : ∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ₂ (ρ₁ v) = v := by
      intro v hv; have := hf_id v hv; simp [Function.comp] at this; exact this
    have hC'_fix : C'.image (ρ₂ ∘ ρ₁) = C' := by
      ext v; simp only [Finset.mem_image, Function.comp]; constructor
      · rintro ⟨w, hw, rfl⟩; rw [hf_id' w ⟨C', hC'_A.1, hw⟩]; exact hw
      · intro hv; exact ⟨v, hv, hf_id' v ⟨C', hC'_A.1, hv⟩⟩

    have hC'_fold : C'.image (ρ₂ ∘ ρ₁) = C := by
      rw [show C'.image (ρ₂ ∘ ρ₁) = (C'.image ρ₁).image ρ₂ from by rw [← Finset.image_image]]
      have hC_ρ₁ : C.image ρ₁ = C :=
        AptFoldingFromRetraction.retraction_fixes_face hρ₁_fix hC_A'
      have h_cases := hρ₁_adj C C' hadj_K
      rw [hC_ρ₁] at h_cases
      cases h_cases with
      | inl h_eq =>
        rw [← h_eq, AptFoldingFromRetraction.retraction_fixes_face hρ₂_fix hC_A.1]
      | inr h_adj_A' =>
        have hF₀_sub_ρ₁C' : F₀ ⊆ C'.image ρ₁ := by
          intro v hv; rw [Finset.mem_image]; exact ⟨v, hF₀_sub_C' hv, hρ₁_fix v ⟨F₀, hF₀_A', hv⟩⟩
        have hF₀_sub_ρ₂ρ₁C' : F₀ ⊆ (C'.image ρ₁).image ρ₂ := by
          intro v hv; rw [Finset.mem_image]; exact ⟨v, hF₀_sub_ρ₁C' hv, hρ₂_fix v ⟨F₀, hF₀_A, hv⟩⟩
        have hρ₁C'_A'_max : A'.IsMaximal (C'.image ρ₁) := hρ₁_ch C' hC'_K
        have hρ₁C'_K : K.toSimplicialComplex.IsMaximal (C'.image ρ₁) :=
          pre.maximal_in_apt_is_maximal A' hA' (C'.image ρ₁) hρ₁C'_A'_max
        have hρ₂ρ₁C'_A_max : A.IsMaximal ((C'.image ρ₁).image ρ₂) :=
          hρ₂_ch (C'.image ρ₁) hρ₁C'_K
        obtain ⟨B, hB, hρ₁C'_B, hC'_B⟩ :=
          pre.contains_pair (C'.image ρ₁) C' hρ₁C'_K hC'_K
        have h_ne_C' : (C'.image ρ₁).image ρ₂ ≠ C' := by
          intro h_eq_C'
          have h_sub : C'.image ρ₁ ⊆ C' := by
            intro v hv; rw [Finset.mem_image] at hv; obtain ⟨w, hw, rfl⟩ := hv
            have hρ₂_ρ₁w : ρ₂ (ρ₁ w) ∈ C' := by
              rw [← h_eq_C']; exact Finset.mem_image_of_mem ρ₂ (Finset.mem_image_of_mem ρ₁ hw)
            have hρ₁w_in_B : ∃ s ∈ B.faces, ρ₁ w ∈ s :=
              ⟨C'.image ρ₁, hρ₁C'_B, Finset.mem_image_of_mem ρ₁ hw⟩
            have hu_in_B : ∃ s ∈ B.faces, (ρ₂ (ρ₁ w)) ∈ s := ⟨C', hC'_B, hρ₂_ρ₁w⟩
            have : ρ₁ w = ρ₂ (ρ₁ w) :=
              hρ₂_inj B hB hC'_B (ρ₁ w) (ρ₂ (ρ₁ w)) hρ₁w_in_B hu_in_B
                (hρ₂_fix (ρ₂ (ρ₁ w)) ⟨C', hC'_A.1, hρ₂_ρ₁w⟩).symm
            rw [this]; exact hρ₂_ρ₁w
          have h_ρ₁C'_eq_C' : C'.image ρ₁ = C' := hρ₁C'_K.2 C' hC'_K.1 h_sub
          have hC'_A'_max : A'.IsMaximal C' := by rw [← h_ρ₁C'_eq_C']; exact hρ₁C'_A'_max
          have hE_A'_max : A'.IsMaximal E :=
            pre.building_maximal_in_apt_is_apt_maximal A' hA' E hE_A' hE_K_max
          have hF₀_C_A' : A'.IsFacet F₀ C := ⟨⟨hF₀_A', hC_A'_max.1, hF₀_K_C.1.2.2⟩, hF₀_K_C.2⟩
          have hC'_A'_face : C' ∈ A'.faces := hC'_A'_max.1
          have hF₀_C'_A' : A'.IsFacet F₀ C' :=
            ⟨⟨A'.down_closed hC'_A'_face hF₀_sub_C'
                (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1),
              hC'_A'_face, hF₀_sub_C'⟩, hF₀_K_C'.2⟩
          have hF₀_E_A' : A'.IsFacet F₀ E :=
            ⟨⟨A'.down_closed hE_A' hF₀_K_E.1.2.2
                (K.toSimplicialComplex.nonempty_of_mem F₀ hF₀_K_C.1.1),
              hE_A', hF₀_K_E.1.2.2⟩, hF₀_K_E.2⟩
          exact hE_ne_C' (thin_unique_other_chamber_pre K pre hA' hC_A'_max hF₀_C_A'
            hC'_A'_max hne.symm hF₀_C'_A' hE_A'_max hE_ne_C hF₀_E_A').symm
        have h_C_or_C' := apt_chamber_with_facet_is_C_or_C_pre K pre hA hC_A hC'_A
          hρ₂ρ₁C'_A_max hne hF₀_C_A hF₀_C'_A hF₀_sub_ρ₂ρ₁C'
        cases h_C_or_C' with
        | inl h_eq_C => exact h_eq_C
        | inr h_eq_C' => exact absurd h_eq_C' h_ne_C'
    exact hne (hC'_fold ▸ hC'_fix)

/-- Construct a folding from a simplicial map fixing a chamber and sending
its panel-mate to itself — the third-chamber map of a thick complex. -/
theorem folding_from_simplicial_map
    (cc : ChamberComplex V) (hthin : cc.IsThin)
    (f : V → V)
    (hface : ∀ s ∈ cc.toSimplicialComplex.faces,
      s.image f ∈ cc.toSimplicialComplex.faces)
    (hidempotent : ∀ v, f (f v) = f v)
    (hchamberMap : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      cc.toSimplicialComplex.IsMaximal (D.image f))
    (hpreservesFacets : ∀ F D, cc.toSimplicialComplex.IsFacet F D →
      cc.toSimplicialComplex.IsFacet (F.image f) (D.image f))
    (htwoToOne : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      D.image f = D →
      ∃! D', cc.toSimplicialComplex.IsMaximal D' ∧ D' ≠ D ∧ D'.image f = D)
    (hstutter_contradicts_minimality :
      ∀ (A B : Finset V),
        cc.toSimplicialComplex.IsMaximal A → A.image f = A →
        cc.toSimplicialComplex.IsMaximal B → B.image f = B →
        ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A B →
        g.length = galleryDist cc.toSimplicialComplex A B →
        ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers →
          cc.toSimplicialComplex.Adjacent Ci Ci1 →
          Ci1.image f = Ci.image f → False)
    (C C' : Finset V)
    (hadj : cc.toSimplicialComplex.Adjacent C C')
    (hfC : C.image f = C)
    (hfC' : C'.image f = C) :
    ∃ fold : Folding cc,
      C.image fold.morph.toFun = C ∧ C'.image fold.morph.toFun = C := by

  have hCmax : cc.toSimplicialComplex.IsMaximal C := hadj.1
  have hC'max : cc.toSimplicialComplex.IsMaximal C' := hadj.2.1
  have hne : C ≠ C' := hadj.2.2.1
  obtain ⟨F, hFC, hFC'⟩ := hadj.2.2.2

  let morph : SimplicialComplex.Morphism cc.toSimplicialComplex cc.toSimplicialComplex :=
    ⟨f, hface⟩

  have fixes_pointwise_of_fixed : ∀ (D : Finset V), D.image f = D → ∀ v ∈ D, f v = v := by
    intro D hD v hv
    rw [← hD] at hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    rw [← huv, hidempotent]

  have hC'moved : C'.image f ≠ C' := by
    rw [hfC']; exact fun h => hne (h ▸ rfl)

  have hnot_id : ∃ D, cc.toSimplicialComplex.IsMaximal D ∧ D.image f ≠ D := by
    exact ⟨C', hC'max, hC'moved⟩

  have hstutter_at_boundary :
      ∀ (Ci Ci1 : Finset V),
        cc.toSimplicialComplex.Adjacent Ci Ci1 →
        (cc.toSimplicialComplex.IsMaximal Ci ∧ Ci.image f = Ci) →
        Ci1.image f ≠ Ci1 →
        Ci1.image f = Ci := by
    intro Ci Ci1 hadj_pair ⟨hCimax, hfCi⟩ hCi1moved
    obtain ⟨_, hCi1max, hne_pair, G, hGCi, hGCi1⟩ := hadj_pair

    have hfix := fixes_pointwise_of_fixed Ci hfCi
    have hfG : G.image f = G := by
      ext v; simp only [Finset.mem_image]; constructor
      · rintro ⟨w, hw, rfl⟩; rwa [hfix w (hGCi.1.2.2 hw)]
      · intro hv; exact ⟨v, hv, hfix v (hGCi.1.2.2 hv)⟩

    have hfGfCi1 := hpreservesFacets G Ci1 hGCi1
    rw [hfG] at hfGfCi1

    have hfCi1max := hchamberMap Ci1 hCi1max

    obtain ⟨D', ⟨_, _, _⟩, hD'uniq⟩ := hthin G Ci hGCi hCimax


    by_contra hfCi1_ne_Ci
    have hCi1_eq_D' : Ci1 = D' := hD'uniq Ci1 ⟨hne_pair.symm, hGCi1, hCi1max⟩
    have : Ci1.image f = D' :=
      hD'uniq (Ci1.image f) ⟨hfCi1_ne_Ci, hfGfCi1, hfCi1max⟩
    rw [← hCi1_eq_D'] at this
    exact hCi1moved this

  have hexists_boundary : ∃ A B, cc.toSimplicialComplex.Adjacent A B ∧
      A.image f = A ∧ B.image f ≠ B := by
    exact ⟨C, C', hadj, hfC, hC'moved⟩


  have hgallery_exits :
      ∀ (A B : Finset V),
        cc.toSimplicialComplex.IsMaximal A → A.image f = A →
        cc.toSimplicialComplex.IsMaximal B → B.image f = B →
        ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A B →
        ∀ (E : Finset V), E ∈ g.chambers → E.image f ≠ E →
        ∃ Ci Ci1, Ci ∈ g.chambers ∧ Ci1 ∈ g.chambers ∧
          cc.toSimplicialComplex.Adjacent Ci Ci1 ∧
          (cc.toSimplicialComplex.IsMaximal Ci ∧ Ci.image f = Ci) ∧
          ¬(cc.toSimplicialComplex.IsMaximal Ci1 ∧ Ci1.image f = Ci1) := by
    intro A' B' hA'max hfA' hB'max hfB' g hconn E hE_mem hE_moved

    let P := fun (D : Finset V) => cc.toSimplicialComplex.IsMaximal D ∧ D.image f = D
    have hl_ne : g.chambers ≠ [] := by
      intro h; have := g.length_pos; rw [h] at this; simp at this
    have hhead_P : P (g.chambers.head hl_ne) := by
      have := hconn.1
      rw [List.head?_eq_some_head hl_ne] at this
      simp at this; rw [this]; exact ⟨hA'max, hfA'⟩
    have hE_notP : ∃ e ∈ g.chambers, ¬P e := by
      refine ⟨E, hE_mem, ?_⟩
      intro ⟨_, hfE⟩; exact hE_moved hfE
    obtain ⟨a, b, ha, hb, hadj_ab, hPa, hPb⟩ :=
      chain_transition cc.toSimplicialComplex.Adjacent P g.chambers
        g.adjacent_consecutive hl_ne hhead_P hE_notP
    exact ⟨a, b, ha, hb, hadj_ab, hPa, hPb⟩

  exact ⟨⟨morph, hchamberMap, hpreservesFacets, hidempotent, hnot_id,
    htwoToOne, hexists_boundary, hgallery_exits, hstutter_at_boundary,
    hstutter_contradicts_minimality⟩, hfC, hfC'⟩

/-- Every apartment of a thick chamber complex has sufficient foldings
(every adjacent pair is collapsed by some folding). -/
theorem apt_has_sufficient_foldings
    (K : ChamberComplex V) (hK_thick : K.IsThick)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (hcc_thin : cc.IsThin) :
    HasSufficientFoldings cc := by

  intro C C' hadj_cc

  have hadj_A : A.Adjacent C C' := hcc_eq ▸ hadj_cc

  have hC_A_max : A.IsMaximal C := hcc_eq ▸ hadj_cc.1
  have hC'_A_max : A.IsMaximal C' := hcc_eq ▸ hadj_cc.2.1

  obtain ⟨f, hfC, hfC', hf_face, hf_idem, hf_cmap, hf_pfacets, hf_twoToOne, hf_stutter⟩ :=
    exists_map_fixing_sending_adj_pre K hK_thick pre A hA C C' hC_A_max hC'_A_max hadj_A

  have hadj_A' : A.Adjacent C' C := by
    obtain ⟨h1, h2, h3, F, hFC, hFC'⟩ := hadj_A
    exact ⟨h2, h1, Ne.symm h3, F, hFC', hFC⟩
  obtain ⟨f', hf'C', hf'C, hf'_face, hf'_idem, hf'_cmap, hf'_pfacets, hf'_twoToOne, hf'_stutter⟩ :=
    exists_map_fixing_sending_adj_pre K hK_thick pre A hA C' C hC'_A_max hC_A_max hadj_A'

  have hf_face_cc : ∀ s ∈ cc.toSimplicialComplex.faces,
      s.image f ∈ cc.toSimplicialComplex.faces := by
    intro s hs; rw [hcc_eq] at hs ⊢; exact hf_face s hs
  have hf_cmap_cc : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      cc.toSimplicialComplex.IsMaximal (D.image f) := by
    intro D hD; rw [hcc_eq] at hD ⊢; exact hf_cmap D hD
  have hf_pfacets_cc : ∀ F D, cc.toSimplicialComplex.IsFacet F D →
      cc.toSimplicialComplex.IsFacet (F.image f) (D.image f) := by
    intro F D hFD; rw [hcc_eq] at hFD ⊢; exact hf_pfacets F D hFD
  have hf_twoToOne_cc : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      D.image f = D →
      ∃! D', cc.toSimplicialComplex.IsMaximal D' ∧ D' ≠ D ∧ D'.image f = D := by
    exact hf_twoToOne cc hcc_eq
  have hf_stutter_cc :
      ∀ (A₀ B : Finset V),
        cc.toSimplicialComplex.IsMaximal A₀ → A₀.image f = A₀ →
        cc.toSimplicialComplex.IsMaximal B → B.image f = B →
        ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A₀ B →
        g.length = galleryDist cc.toSimplicialComplex A₀ B →
        ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers →
          cc.toSimplicialComplex.Adjacent Ci Ci1 →
          Ci1.image f = Ci.image f → False := by
    exact hf_stutter cc hcc_eq
  have hf'_face_cc : ∀ s ∈ cc.toSimplicialComplex.faces,
      s.image f' ∈ cc.toSimplicialComplex.faces := by
    intro s hs; rw [hcc_eq] at hs ⊢; exact hf'_face s hs
  have hf'_cmap_cc : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      cc.toSimplicialComplex.IsMaximal (D.image f') := by
    intro D hD; rw [hcc_eq] at hD ⊢; exact hf'_cmap D hD
  have hf'_pfacets_cc : ∀ F D, cc.toSimplicialComplex.IsFacet F D →
      cc.toSimplicialComplex.IsFacet (F.image f') (D.image f') := by
    intro F D hFD; rw [hcc_eq] at hFD ⊢; exact hf'_pfacets F D hFD
  have hf'_twoToOne_cc : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      D.image f' = D →
      ∃! D', cc.toSimplicialComplex.IsMaximal D' ∧ D' ≠ D ∧ D'.image f' = D := by
    exact hf'_twoToOne cc hcc_eq
  have hf'_stutter_cc :
      ∀ (A₀ B : Finset V),
        cc.toSimplicialComplex.IsMaximal A₀ → A₀.image f' = A₀ →
        cc.toSimplicialComplex.IsMaximal B → B.image f' = B →
        ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A₀ B →
        g.length = galleryDist cc.toSimplicialComplex A₀ B →
        ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers →
          cc.toSimplicialComplex.Adjacent Ci Ci1 →
          Ci1.image f' = Ci.image f' → False := by
    exact hf'_stutter cc hcc_eq

  obtain ⟨fold_f, hfold_fC, hfold_fC'⟩ :=
    folding_from_simplicial_map cc hcc_thin f hf_face_cc hf_idem hf_cmap_cc hf_pfacets_cc
      hf_twoToOne_cc hf_stutter_cc C C' hadj_cc hfC hfC'

  have hadj_cc' : cc.toSimplicialComplex.Adjacent C' C := by
    obtain ⟨h1, h2, h3, F, hFC, hFC'⟩ := hadj_cc
    exact ⟨h2, h1, Ne.symm h3, F, hFC', hFC⟩
  obtain ⟨fold_f', hfold_f'C', hfold_f'C⟩ :=
    folding_from_simplicial_map cc hcc_thin f' hf'_face_cc hf'_idem hf'_cmap_cc hf'_pfacets_cc
      hf'_twoToOne_cc hf'_stutter_cc C' C hadj_cc' hf'C' hf'C

  exact ⟨fold_f, fold_f', hfold_fC, hfold_fC', hfold_f'C', hfold_f'C⟩

/-- Main theorem: thickness of a chamber complex implies that every
apartment has sufficient foldings — discharging the
`ThicknessImpliesAptStructureHyp`. -/
theorem thickness_implies_apt_structure_hyp :
    ThicknessImpliesAptStructureHyp V := by
  intro K hThick pre A hA

  obtain ⟨cc, hcc_eq, hcc_thin⟩ := apt_thinness_from_thickness K hThick pre A hA

  exact ⟨cc, hcc_eq, hcc_thin, apt_has_sufficient_foldings K hThick pre A hA cc hcc_eq hcc_thin⟩

end ThicknessFoldings
