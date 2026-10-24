/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Link
import Lemma.Finset.Disjoint.of.In_FacesLinkComplex.In_Faces
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.IsMaximalUnion.of.IsMaximalLinkComplex.In_Faces
import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.LinkBuildingIsoHelper
import Lemma.Finset.IsMaximalLinkComplex.of.IsMaximalUnion.In_FacesLinkComplex.In_Faces
import Lemma.Finset.IsFacetToSimplicialComplexAndIsMaximalToSimplicialComplex.Unique.of.IsMaximalToSimplicialComplex.IsFacetToSimplicialComplex.IsThin
import Lemma.Finset.IsMaximalToSimplicialComplexToChamberComplexUnion.of.IsMaximalLinkComplexToSimplicialComplexToChamberComplex.In_FacesToSimplicialComplexToChamberComplex

open scoped Classical


variable {V : Type} [DecidableEq V]

namespace SimplicialComplex

/-- When $\tau$ is disjoint from $\sigma$, the set difference $(\sigma \cup \tau) \setminus
(\sigma \cup F)$ equals $\tau \setminus F$. -/
theorem sdiff_union_eq_sdiff_of_disjoint' {σ F τ : Finset V}
    (_hF_disj : Disjoint σ F) (hτ_disj : Disjoint σ τ) :
    (σ ∪ τ) \ (σ ∪ F) = τ \ F := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (Or.inl h1) h2
    · exact ⟨h1, fun hv => h2 (Or.inr hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr h1, fun h => h.elim (fun h => Finset.disjoint_right.mp hτ_disj h1 h) h2⟩

/-- A maximal face $\tau$ of the link $\mathrm{lk}_K(\sigma)$ lifts to a maximal face $\sigma \cup
\tau$ of the ambient complex $K$. -/
theorem union_maximal_of_linkComplex_maximal' {K : SimplicialComplex V} {σ : Finset V}
    (hσ : σ ∈ K.faces) {τ : Finset V}
    (hτ_max : (K.linkComplex σ hσ).IsMaximal τ) :
    K.IsMaximal (σ ∪ τ) := by
  have hτ_link := hτ_max.1
  rw [mem_linkComplex_iff] at hτ_link
  refine ⟨hτ_link.2.2, fun w hw h_sub => ?_⟩
  have hσw : σ ⊆ w := Finset.subset_union_left.trans h_sub
  by_cases hne : (w \ σ).Nonempty
  · have hw_link := mem_linkComplex_of_sdiff K σ hσ w hw hσw hne
    have hτ_sub : τ ⊆ w \ σ := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨h_sub (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hτ_link.2.1 hv⟩
    rw [hτ_max.2 (w \ σ) hw_link hτ_sub, Finset.union_sdiff_of_subset hσw]
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    exfalso
    obtain ⟨v, hv⟩ := hτ_link.1
    exact Finset.disjoint_right.mp hτ_link.2.1 hv (hne (h_sub (Finset.mem_union_right σ hv)))

/-- The converse direction: if $\sigma \cup \tau$ is maximal in $K$ and $\tau$ lies in the link of
$\sigma$, then $\tau$ is maximal in $\mathrm{lk}_K(\sigma)$. -/
theorem linkComplex_maximal_of_union_maximal' {K : SimplicialComplex V} {σ : Finset V}
    (hσ : σ ∈ K.faces) {τ : Finset V}
    (hτ_link : τ ∈ (K.linkComplex σ hσ).faces)
    (hστ_max : K.IsMaximal (σ ∪ τ)) :
    (K.linkComplex σ hσ).IsMaximal τ := by
  have hτ_data := (mem_linkComplex_iff K σ hσ τ).mp hτ_link
  refine ⟨hτ_link, fun y hy hτy => ?_⟩
  have hy_data := (mem_linkComplex_iff K σ hσ y).mp hy
  have h_eq := hστ_max.2 (σ ∪ y) hy_data.2.2 (Finset.union_subset_union_right hτy)
  ext v
  constructor
  · intro hv
    have := h_eq ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hτ_data.2.1 hv)) id
  · intro hv
    have := h_eq.symm ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hy_data.2.1 hv)) id

/-- The link operation is monotone with respect to subcomplex inclusion: if $A$ is a subcomplex of
$K$, then $\mathrm{lk}_A(\sigma)$ is a subcomplex of $\mathrm{lk}_K(\sigma)$. -/
theorem linkComplex_sub {K A : SimplicialComplex V}
    (hA : IsSubcomplex A K) (σ : Finset V) (hσK : σ ∈ K.faces) (hσA : σ ∈ A.faces) :
    IsSubcomplex (A.linkComplex σ hσA) (K.linkComplex σ hσK) := by
  intro τ hτ
  rw [mem_linkComplex_iff] at hτ ⊢
  exact ⟨hτ.1, hτ.2.1, hA hτ.2.2⟩

end SimplicialComplex

/-- Every face of the link $\mathrm{lk}_K(\sigma)$ extends to a maximal face of the link, witnessed
by extending a chamber of $K$ containing $\sigma \cup s$ and removing $\sigma$. -/
theorem link_exists_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C) :
    ∀ s ∈ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).faces,
      ∃ C, (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C ∧ s ⊆ C := by
  set K := b.toChamberComplex.toSimplicialComplex
  set lk := K.linkComplex σ hσ
  intro s hs
  have hs_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ s).mp hs
  obtain ⟨C, hC_max, hσs_sub⟩ := b.toChamberComplex.exists_maximal (σ ∪ s) hs_data.2.2
  have hσ_sub_C : σ ⊆ C := Finset.subset_union_left.trans hσs_sub
  have hne : (C \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hs_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩⟩
  have hCσ_link := SimplicialComplex.mem_linkComplex_of_sdiff K σ hσ C hC_max.1 hσ_sub_C hne
  have hC_eq : σ ∪ (C \ σ) = C := Finset.union_sdiff_of_subset hσ_sub_C
  have hCσ_max_K : K.IsMaximal (σ ∪ (C \ σ)) := by rw [hC_eq]; exact hC_max
  have hCσ_max_lk : lk.IsMaximal (C \ σ) :=
    SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hCσ_link hCσ_max_K
  have hs_sub : s ⊆ C \ σ := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩
  exact ⟨C \ σ, hCσ_max_lk, hs_sub⟩

/-- An apartment isomorphism $\varphi : A \to B$ fixing a chamber $C$ pointwise (and a face $x$
pointwise) is injective on the vertex set covered by faces of $A$, by reduction to the unique
labelling property. -/
theorem iso_exists_injective
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (B : SimplicialComplex V) (hB : B ∈ b.apartmentSystem.apartments)
    (x : Finset V) (hxA : x ∈ A.faces) (hxB : x ∈ B.faces)
    (C : Finset V) (hC_max : A.IsMaximal C) (hCB : C ∈ B.faces)
    (φ : SimplicialMap A B)
    (hφ_fix_x : ∀ v ∈ x, φ.toFun v = v)
    (hφ_fix_C : ∀ v ∈ C, φ.toFun v = v) :
    ∀ (v₁ v₂ : V), (∃ s ∈ A.faces, v₁ ∈ s) → (∃ s ∈ A.faces, v₂ ∈ s) →
    φ.toFun v₁ = φ.toFun v₂ → v₁ = v₂ := by


  suffices hid : ∀ (v : V), (∃ s ∈ A.faces, v ∈ s) → φ.toFun v = v by
    intro v₁ v₂ hv₁ hv₂ heq
    rw [hid v₁ hv₁, hid v₂ hv₂] at heq
    exact heq

  intro v ⟨s, hs, hv⟩

  set lab₁ : Finset V → Finset (V × V) := fun t => t.image (fun w => (w, w)) with lab₁_def
  set lab₂ : Finset V → Finset (V × V) := fun t => t.image (fun w => (w, φ.toFun w)) with lab₂_def

  have hinj₁ : Function.Injective (fun w : V => (w, w)) :=
    fun a b h => (Prod.mk.inj h).1
  have hinj₂ : Function.Injective (fun w : V => (w, φ.toFun w)) :=
    fun a b h => (Prod.mk.inj h).1

  have hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t := by
    intro s' t' _ _ hst
    exact (Finset.image_ssubset_image hinj₁).mpr hst
  have hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t := by
    intro s' t' _ _ hst
    exact (Finset.image_ssubset_image hinj₂).mpr hst

  have hagree : lab₂ C = Finset.image id (lab₁ C) := by
    simp only [Finset.image_id]

    simp only [lab₁_def, lab₂_def]
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨u, hu, rfl, rfl⟩
      exact ⟨u, hu, rfl, (hφ_fix_C u hu).symm⟩
    · rintro ⟨u, hu, rfl, rfl⟩
      exact ⟨u, hu, rfl, hφ_fix_C u hu⟩

  obtain ⟨_, huniq⟩ := b.apartmentSystem.apt_unique_labelling A hA
    (V × V) (V × V) lab₁ lab₂ hmono₁ hmono₂ C hC_max
  have hall := huniq id Function.bijective_id hagree s hs


  simp only [Finset.image_id] at hall

  have hv_mem : (v, φ.toFun v) ∈ lab₂ s := Finset.mem_image_of_mem _ hv
  rw [hall] at hv_mem
  rw [lab₁_def] at hv_mem
  simp only [Finset.mem_image, Prod.mk.injEq] at hv_mem
  obtain ⟨w, _, rfl, hw_eq⟩ := hv_mem
  exact hw_eq.symm

/-- Isomorphism axiom for link apartments: given link apartments $A', B'$ sharing a face $x$ and
a chamber $C \subseteq A' \cap B'$ with $A'.IsMaximal C$, an ambient apartment isomorphism
restricts to an isomorphism of link apartments fixing $x$ and $C$. -/
theorem link_iso_exists
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A' ∈ link_apts, ∀ B' ∈ link_apts,
      ∀ x, x ∈ A'.faces → x ∈ B'.faces →
      ∀ C, A'.IsMaximal C → C ∈ B'.faces →
      ∃ φ : SimplicialMap A' B',
        (∀ v ∈ x, φ.toFun v = v) ∧ (∀ v ∈ C, φ.toFun v = v) := by
  intro A' hA' B' hB' x hx_A' hx_B' C hC_max_A' hC_B'
  rw [h_link_apts] at hA' hB'
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hA'
  obtain ⟨B, hB_apt, hσB, rfl⟩ := hB'
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem

  have hx_A_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA x).mp hx_A'
  have hx_B_data := (SimplicialComplex.mem_linkComplex_iff B σ hσB x).mp hx_B'
  have hC_A_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA C).mp hC_max_A'.1
  have hC_B_data := (SimplicialComplex.mem_linkComplex_iff B σ hσB C).mp hC_B'
  have hσx_A : (σ ∪ x) ∈ A.faces := hx_A_data.2.2
  have hσx_B : (σ ∪ x) ∈ B.faces := hx_B_data.2.2
  have hσC_A : (σ ∪ C) ∈ A.faces := hC_A_data.2.2
  have hσC_B : (σ ∪ C) ∈ B.faces := hC_B_data.2.2
  have hσC_max_A : A.IsMaximal (σ ∪ C) :=
    SimplicialComplex.union_maximal_of_linkComplex_maximal' hσA hC_max_A'

  obtain ⟨φ_amb, hφ_fix_x, hφ_fix_C⟩ := 𝒜.iso_exists A hA_apt B hB_apt (σ ∪ x)
    hσx_A hσx_B (σ ∪ C) hσC_max_A hσC_B

  have hφ_fix_σ : ∀ v ∈ σ, φ_amb.toFun v = v :=
    fun v hv => hφ_fix_x v (Finset.mem_union_left x hv)

  have hφ_inj := iso_exists_injective b A hA_apt B hB_apt (σ ∪ x)
    hσx_A hσx_B (σ ∪ C) hσC_max_A hσC_B φ_amb hφ_fix_x hφ_fix_C


  have hφ_disj : ∀ s, s ∈ (A.linkComplex σ hσA).faces →
      Disjoint σ (s.image φ_amb.toFun) := by
    intro s hs
    have hs_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA s).mp hs
    rw [Finset.disjoint_left]
    intro w hw hw_img
    rw [Finset.mem_image] at hw_img
    obtain ⟨v, hv, hφv⟩ := hw_img


    have hφw : φ_amb.toFun w = w := hφ_fix_σ w hw

    have hv_eq_w : v = w := by
      apply hφ_inj v w
      · exact ⟨σ ∪ s, hs_data.2.2, Finset.mem_union_right σ hv⟩
      · exact ⟨σ, hσA, hw⟩
      · rw [hφv, hφw]

    exact Finset.disjoint_right.mp hs_data.2.1 (hv_eq_w ▸ hv) hw

  refine ⟨⟨φ_amb.toFun, fun s hs => ?_⟩, ?_, ?_⟩
  ·
    have hs_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA s).mp hs
    rw [SimplicialComplex.mem_linkComplex_iff B σ hσB (s.image φ_amb.toFun)]
    refine ⟨?_, hφ_disj s hs, ?_⟩
    ·
      obtain ⟨v, hv⟩ := hs_data.1
      exact ⟨φ_amb.toFun v, Finset.mem_image_of_mem φ_amb.toFun hv⟩
    ·
      have h1 : σ ∪ s ∈ A.faces := hs_data.2.2
      have h2 : (σ ∪ s).image φ_amb.toFun ∈ B.faces := φ_amb.map_face (σ ∪ s) h1

      rw [Finset.image_union] at h2
      have hσ_img : σ.image φ_amb.toFun = σ := by
        ext v; simp only [Finset.mem_image]
        constructor
        · rintro ⟨w, hw, rfl⟩; rw [hφ_fix_σ w hw]; exact hw
        · intro hv; exact ⟨v, hv, hφ_fix_σ v hv⟩
      rw [hσ_img] at h2
      exact h2
  ·
    intro v hv
    exact hφ_fix_x v (Finset.mem_union_right σ hv)
  ·
    intro v hv
    exact hφ_fix_C v (Finset.mem_union_right σ hv)

/-- A maximal face of a link apartment is also maximal in the link of the whole building, by
lifting through the ambient apartment structure. -/
theorem link_maximal_in_apt_is_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∀ C, A.IsMaximal C →
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C := by
  intro L hL C hC_max_L
  rw [h_link_apts] at hL
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem

  have hσC_max_A : A.IsMaximal (σ ∪ C) :=
    SimplicialComplex.union_maximal_of_linkComplex_maximal' hσA hC_max_L

  have hσC_max_K : K.IsMaximal (σ ∪ C) :=
    𝒜.maximal_in_apt_is_maximal A hA_apt (σ ∪ C) hσC_max_A

  have hC_link : C ∈ (K.linkComplex σ hσ).faces :=
    SimplicialComplex.linkComplex_sub (𝒜.sub A hA_apt) σ hσ hσA hC_max_L.1

  exact SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hC_link hσC_max_K

/-- Gallery distance in the link is bounded by the gallery distance of the lifted chambers in the
ambient building: $d_{\mathrm{lk}}(C, D) \leq d_K(\sigma \cup C, \sigma \cup D)$. -/
theorem link_gallery_dist_le
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_cc : ChamberComplex V)
    (h_link_cc : link_cc.toSimplicialComplex =
      b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ)
    (C D : Finset V)
    (hC_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C)
    (hD_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D) :
    galleryDist link_cc.toSimplicialComplex C D ≤
      galleryDist b.toChamberComplex.toSimplicialComplex (σ ∪ C) (σ ∪ D) :=
  link_gallery_dist_le_axiom b σ hσ hσ_proper link_cc h_link_cc C D hC_max hD_max

/-- Gallery convexity axiom for link apartments: any minimal gallery in the link between two
chambers of a link apartment $A$ stays entirely inside $A$, proven by lifting the gallery to the
ambient building and applying ambient gallery convexity. -/
theorem link_gallery_convex
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_cc : ChamberComplex V)
    (h_link_cc : link_cc.toSimplicialComplex =
      b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∀ C D : Finset V,
      C ∈ A.faces → link_cc.toSimplicialComplex.IsMaximal C →
      D ∈ A.faces → link_cc.toSimplicialComplex.IsMaximal D →
      ∀ g : Gallery link_cc.toSimplicialComplex,
        g.Connects C D →
        g.length = galleryDist link_cc.toSimplicialComplex C D →
        ∀ E ∈ g.chambers, E ∈ A.faces := by
  intro L hL C D hC_L hC_max hD_L hD_max g hg_conn hg_min E hE_g
  rw [h_link_apts] at hL
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem

  have hE_max_lk : link_cc.toSimplicialComplex.IsMaximal E := g.all_maximal E hE_g
  rw [h_link_cc] at hE_max_lk hC_max hD_max
  have hC_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA C).mp hC_L
  have hD_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA D).mp hD_L
  have hE_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ E).mp hE_max_lk.1


  have hσC_A : (σ ∪ C) ∈ A.faces := hC_data.2.2
  have hσD_A : (σ ∪ D) ∈ A.faces := hD_data.2.2
  have hσC_max_K : K.IsMaximal (σ ∪ C) :=
    SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hC_max
  have hσD_max_K : K.IsMaximal (σ ∪ D) :=
    SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hD_max


  suffices hσE_A : (σ ∪ E) ∈ A.faces by
    rw [SimplicialComplex.mem_linkComplex_iff A σ hσA E]
    exact ⟨hE_data.1, hE_data.2.1, hσE_A⟩


  let lifted_chambers := g.chambers.map (σ ∪ ·)

  have h_all_max : ∀ X ∈ lifted_chambers, K.IsMaximal X := by
    intro X hX
    rw [List.mem_map] at hX
    obtain ⟨Y, hY_mem, rfl⟩ := hX
    have hY_max := g.all_maximal Y hY_mem
    rw [h_link_cc] at hY_max
    exact SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hY_max

  have h_adj_lift : ∀ X Y, link_cc.toSimplicialComplex.Adjacent X Y →
      K.Adjacent (σ ∪ X) (σ ∪ Y) := by
    intro X Y ⟨hX_max, hY_max, hne, F, hFX, hFY⟩
    rw [h_link_cc] at hX_max hY_max hFX hFY
    refine ⟨SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hX_max,
            SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hY_max, ?_, σ ∪ F, ?_, ?_⟩
    · intro h_eq
      apply hne
      have hX_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ X).mp hX_max.1
      have hY_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ Y).mp hY_max.1
      ext v
      constructor
      · intro hv
        have : v ∈ σ ∪ X := Finset.mem_union_right σ hv
        rw [h_eq] at this
        exact (Finset.mem_union.mp this).elim
          (fun h => absurd h (Finset.disjoint_right.mp hX_data.2.1 hv)) id
      · intro hv
        have : v ∈ σ ∪ Y := Finset.mem_union_right σ hv
        rw [← h_eq] at this
        exact (Finset.mem_union.mp this).elim
          (fun h => absurd h (Finset.disjoint_right.mp hY_data.2.1 hv)) id
    ·
      have hF_data := hFX.1
      have hFX_card := hFX.2
      have hF_in_lk := hF_data.1
      have hF_face_X := hF_data.2.1
      have hF_sub_X := hF_data.2.2
      rw [SimplicialComplex.mem_linkComplex_iff K σ hσ F] at hF_in_lk
      constructor
      · exact ⟨hF_in_lk.2.2, (SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hX_max).1,
              Finset.union_subset_union_right hF_sub_X⟩
      · rw [SimplicialComplex.sdiff_union_eq_sdiff_of_disjoint' hF_in_lk.2.1
            ((SimplicialComplex.mem_linkComplex_iff K σ hσ X).mp hX_max.1).2.1]
        exact hFX_card
    ·
      have hF_data := hFY.1
      have hFY_card := hFY.2
      have hF_in_lk := hF_data.1
      have hF_face_Y := hF_data.2.1
      have hF_sub_Y := hF_data.2.2
      rw [SimplicialComplex.mem_linkComplex_iff K σ hσ F] at hF_in_lk
      constructor
      · exact ⟨hF_in_lk.2.2, (SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hY_max).1,
              Finset.union_subset_union_right hF_sub_Y⟩
      · rw [SimplicialComplex.sdiff_union_eq_sdiff_of_disjoint' hF_in_lk.2.1
            ((SimplicialComplex.mem_linkComplex_iff K σ hσ Y).mp hY_max.1).2.1]
        exact hFY_card

  have h_chain : List.IsChain K.Adjacent lifted_chambers := by
    have hc := g.adjacent_consecutive
    exact List.isChain_map_of_isChain (σ ∪ ·) (fun a b hab => h_adj_lift a b hab) hc

  have h_length : lifted_chambers.length = g.chambers.length := by
    simp [lifted_chambers, List.length_map]

  have h_length_pos : lifted_chambers.length > 0 := by
    rw [h_length]; exact g.length_pos
  let lifted_g : Gallery K := ⟨lifted_chambers, h_length_pos, h_all_max, h_chain⟩

  have h_lifted_conn : lifted_g.Connects (σ ∪ C) (σ ∪ D) := by
    constructor
    ·
      simp only [lifted_g, lifted_chambers, List.head?_map]
      rw [hg_conn.1]
      simp
    ·
      simp only [lifted_g, lifted_chambers, List.getLast?_map]
      rw [hg_conn.2]
      simp

  have h_σE_mem : (σ ∪ E) ∈ lifted_g.chambers := by
    simp only [lifted_g, lifted_chambers]
    show σ ∪ E ∈ List.map (σ ∪ ·) g.chambers
    exact List.mem_map_of_mem (f := (σ ∪ ·)) hE_g

  have h_lifted_length : lifted_g.length = g.length := by
    simp only [Gallery.length, lifted_g, lifted_chambers, List.length_map]


  have h_le : galleryDist K (σ ∪ C) (σ ∪ D) ≤ lifted_g.length := by
    by_cases heq : σ ∪ C = σ ∪ D
    · simp [galleryDist, heq]
    · unfold galleryDist; simp only [heq, ↑reduceIte]
      exact Nat.sInf_le ⟨lifted_g, h_lifted_conn, rfl⟩
  have h_ge : lifted_g.length ≤ galleryDist K (σ ∪ C) (σ ∪ D) := by
    rw [h_lifted_length, hg_min]
    exact link_gallery_dist_le b σ hσ hσ_proper link_cc h_link_cc C D hC_max hD_max
  have h_min : lifted_g.length = galleryDist K (σ ∪ C) (σ ∪ D) := Nat.le_antisymm h_le h_ge |>.symm
  exact 𝒜.gallery_convex A hA_apt (σ ∪ C) (σ ∪ D) hσC_A hσC_max_K hσD_A hσD_max_K
    lifted_g h_lifted_conn h_min (σ ∪ E) h_σE_mem

/-- A face that is globally maximal in the link and lies in a link apartment $A$ is also maximal
inside $A$ as a link apartment. -/
theorem link_building_maximal_in_apt_is_apt_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∀ C, C ∈ A.faces →
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C →
      A.IsMaximal C := by
  intro L hL C hC_L hC_max_lk
  rw [h_link_apts] at hL
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem


  have hσC_max_K := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hC_max_lk

  have hC_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA C).mp hC_L
  have hσC_A : (σ ∪ C) ∈ A.faces := hC_data.2.2

  have hσC_max_A := 𝒜.building_maximal_in_apt_is_apt_maximal A hA_apt (σ ∪ C) hσC_A hσC_max_K

  exact SimplicialComplex.linkComplex_maximal_of_union_maximal' hσA hC_L hσC_max_A

/-- Every link apartment is nonempty: it contains $C \setminus \sigma$ for any chamber $C$ of the
ambient apartment that strictly contains $\sigma$. -/
theorem link_apt_nonempty
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∃ s, s ∈ A.faces := by
  intro L hL
  rw [h_link_apts] at hL
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem

  obtain ⟨_, _, cc, hcc_eq, _⟩ := 𝒜.apt_is_coxeter A hA_apt
  have hσ_cc : σ ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hσA
  obtain ⟨C, hC_max_cc, hσ_sub_C⟩ := cc.exists_maximal σ hσ_cc
  have hC_max_A : A.IsMaximal C := hcc_eq ▸ hC_max_cc
  have hC_max_K : K.IsMaximal C := 𝒜.maximal_in_apt_is_maximal A hA_apt C hC_max_A

  have hσ_ne_C : σ ≠ C := by
    intro h_eq
    obtain ⟨C₀, hC₀_max, hσ_sub⟩ := hσ_proper
    have hC_eq_C₀ : C = C₀ := hC_max_K.2 C₀ hC₀_max.1 (h_eq ▸ hσ_sub.1)
    rw [h_eq, hC_eq_C₀] at hσ_sub
    exact hσ_sub.ne rfl
  have hne : (C \ σ).Nonempty := by
    rcases Finset.exists_of_ssubset (Finset.lt_iff_ssubset.mpr (Finset.ssubset_iff_subset_ne.mpr ⟨hσ_sub_C, hσ_ne_C⟩)) with ⟨v, hv, hv'⟩
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩
  exact ⟨C \ σ, SimplicialComplex.mem_linkComplex_of_sdiff A σ hσA C hC_max_A.1 hσ_sub_C hne⟩

/-- Bijectivity of link apartment isomorphisms: for two link apartments sharing a chamber $C$,
there is a bijection $\varphi : V \to V$ inducing an isomorphism between them, obtained from the
ambient apartment isomorphism that fixes $\sigma \cup C$. -/
theorem link_iso_bijective
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∀ A' ∈ link_apts,
      ∀ C, C ∈ A.faces → C ∈ A'.faces → A.IsMaximal C →
      ∃ φ : V → V, Function.Bijective φ ∧
        (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces) := by
  intro L₁ hL₁ L₂ hL₂ C hCL₁ hCL₂ hC_max_L₁
  rw [h_link_apts] at hL₁ hL₂
  obtain ⟨Amb, hAmb_apt, hσAmb, rfl⟩ := hL₁
  obtain ⟨Amb', hAmb'_apt, hσAmb', rfl⟩ := hL₂
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒢 := b.apartmentSystem
  have hσC_max_Amb : Amb.IsMaximal (σ ∪ C) :=
    union_maximal_of_linkComplex_maximal_helper hσAmb hC_max_L₁
  have hC_data_Amb' := (SimplicialComplex.mem_linkComplex_iff Amb' σ hσAmb' C).mp hCL₂
  have hσC_Amb' : (σ ∪ C) ∈ Amb'.faces := hC_data_Amb'.2.2
  have hσC_max_K : K.IsMaximal (σ ∪ C) :=
    𝒢.maximal_in_apt_is_maximal Amb hAmb_apt (σ ∪ C) hσC_max_Amb
  obtain ⟨φ, hφ_bij, hφ_faces, hφ_fix_D⟩ :=
    iso_bijective_fixing_chamber' b Amb hAmb_apt Amb' hAmb'_apt
      (σ ∪ C) hσC_max_Amb.1 hσC_Amb' hσC_max_Amb
  have hφ_id : ∀ s ∈ Amb.faces, s.image φ = s :=
    bij_iso_fixing_chamber_is_id' b Amb Amb' hAmb_apt
      (σ ∪ C) hσC_max_Amb.1 hσC_max_K φ hφ_bij hφ_faces hφ_fix_D
  have hφ_fix_σ : σ.image φ = σ := hφ_id σ hσAmb
  refine ⟨φ, hφ_bij, fun s => ?_⟩
  constructor
  · intro hs
    have hs_data := (SimplicialComplex.mem_linkComplex_iff Amb σ hσAmb s).mp hs
    have hs_Amb : s ∈ Amb.faces :=
      Amb.down_closed hs_data.2.2 Finset.subset_union_right hs_data.1
    rw [SimplicialComplex.mem_linkComplex_iff Amb' σ hσAmb']
    refine ⟨?_, ?_, ?_⟩
    · rw [hφ_id s hs_Amb]; exact hs_data.1
    · rw [hφ_id s hs_Amb]; exact hs_data.2.1
    · rw [hφ_id s hs_Amb]
      have h1 : (σ ∪ s).image φ = σ ∪ s := hφ_id (σ ∪ s) hs_data.2.2
      rw [← h1]
      exact (hφ_faces (σ ∪ s)).mp hs_data.2.2
  · intro hs'
    have hs'_data := (SimplicialComplex.mem_linkComplex_iff Amb' σ hσAmb' (s.image φ)).mp hs'
    have h_key : (σ ∪ s).image φ = σ ∪ s.image φ := by
      rw [Finset.image_union, hφ_fix_σ]
    have hσs_Amb : σ ∪ s ∈ Amb.faces := by
      have : (σ ∪ s).image φ ∈ Amb'.faces := h_key ▸ hs'_data.2.2
      exact (hφ_faces (σ ∪ s)).mpr this
    have hs_ne : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.image_empty] at hs'_data
      exact Finset.not_nonempty_empty hs'_data.1
    have hs_Amb : s ∈ Amb.faces :=
      Amb.down_closed hσs_Amb Finset.subset_union_right hs_ne
    have hφ_s : s.image φ = s := hφ_id s hs_Amb
    rw [SimplicialComplex.mem_linkComplex_iff Amb σ hσAmb]
    refine ⟨hs_ne, ?_, hσs_Amb⟩
    rw [← hφ_s]; exact hs'_data.2.1

/-- The link of a face $\sigma$ in a Coxeter complex carries a natural Coxeter complex structure
on a (smaller) Coxeter system $M'$, realising the parabolic subgroup associated to $\sigma$. -/
theorem link_of_coxeter_complex_is_coxeter
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∃ (B_idx' : Type) (M' : CoxeterMatrix B_idx') (cc' : ChamberComplex V),
      cc'.toSimplicialComplex = A.linkComplex σ hσ ∧
      ∃ (φ' : Finset V → M'.Group),
        (∀ C, (A.linkComplex σ hσ).IsMaximal C →
              ∀ D, (A.linkComplex σ hσ).IsMaximal D → φ' C = φ' D → C = D) ∧
        (∀ w : M'.Group, ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ φ' C = w) ∧
        (∀ C C', (A.linkComplex σ hσ).Adjacent C C' →
          CoxeterComplex.ChamberAdjacent M' (φ' C) (φ' C')) ∧
        cc'.IsThin :=


  coxeter_link_is_sub_coxeter A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper

/-- Each link apartment is itself a Coxeter complex, obtained by applying
`link_of_coxeter_complex_is_coxeter` to the ambient apartment's Coxeter structure. -/
theorem link_apt_is_coxeter
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts,
      ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V),
        cc.toSimplicialComplex = A ∧
        ∃ (φ : Finset V → M.Group),
          (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
          (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
          (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧
          cc.IsThin := by
  intro L hL
  rw [h_link_apts] at hL
  obtain ⟨Amb, hAmb_apt, hσAmb, rfl⟩ := hL

  obtain ⟨B_idx_amb, M_amb, cc_amb, hcc_amb_eq, φ_amb, hinj_amb, hsurj_amb, hadj_amb, _⟩ :=
    b.apartmentSystem.apt_is_coxeter Amb hAmb_apt


  have hσ_proper_Amb : ∃ C, Amb.IsMaximal C ∧ σ ⊂ C := by
    have hσ_cc : σ ∈ cc_amb.toSimplicialComplex.faces := hcc_amb_eq ▸ hσAmb
    obtain ⟨C, hC_max_cc, hσ_sub_C⟩ := cc_amb.exists_maximal σ hσ_cc
    have hC_max_Amb : Amb.IsMaximal C := hcc_amb_eq ▸ hC_max_cc
    have hσ_ne_C : σ ≠ C := by
      intro h_eq
      set K := b.toChamberComplex.toSimplicialComplex
      have hC_max_K : K.IsMaximal C :=
        b.apartmentSystem.maximal_in_apt_is_maximal Amb hAmb_apt C hC_max_Amb
      obtain ⟨C₀, hC₀_max, hσ_sub⟩ := hσ_proper
      have hC_eq_C₀ : C = C₀ := hC_max_K.2 C₀ hC₀_max.1 (h_eq ▸ hσ_sub.1)
      rw [h_eq, hC_eq_C₀] at hσ_sub
      exact hσ_sub.ne rfl
    exact ⟨C, hC_max_Amb, Finset.ssubset_iff_subset_ne.mpr ⟨hσ_sub_C, hσ_ne_C⟩⟩

  exact link_of_coxeter_complex_is_coxeter Amb B_idx_amb M_amb cc_amb hcc_amb_eq
    φ_amb hinj_amb hsurj_amb hadj_amb σ hσAmb hσ_proper_Amb

/-- Any two chambers $C', D'$ of the link both lie in a common link apartment, obtained from an
ambient apartment containing the lifted chambers $\sigma \cup C'$ and $\sigma \cup D'$. -/
theorem link_contains_pair (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA})
    (C' D' : Finset V)
    (hC'_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C')
    (hD'_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D') :
    ∃ A ∈ link_apts, C' ∈ A.faces ∧ D' ∈ A.faces := by
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem
  have hσC'_max := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hC'_max
  have hσD'_max := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hD'_max
  obtain ⟨A, hA_apt, hC'_A, hD'_A⟩ := 𝒜.contains_pair
    (σ ∪ C') (σ ∪ D') hσC'_max hσD'_max
  have hσA : σ ∈ A.faces :=
    A.down_closed hC'_A Finset.subset_union_left (K.nonempty_of_mem σ hσ)
  have h_lk_apt : A.linkComplex σ hσA ∈ link_apts := by
    rw [h_link_apts]; exact ⟨A, hA_apt, hσA, rfl⟩
  have hC'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ C').mp hC'_max.1
  have hD'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ D').mp hD'_max.1
  exact ⟨A.linkComplex σ hσA, h_lk_apt,
    (SimplicialComplex.mem_linkComplex_iff A σ hσA C').mpr ⟨hC'_data.1, hC'_data.2.1, hC'_A⟩,
    (SimplicialComplex.mem_linkComplex_iff A σ hσA D').mpr ⟨hD'_data.1, hD'_data.2.1, hD'_A⟩⟩

/-- Thickness of the link: every facet $F'$ of the link is contained in at least three distinct
chambers, deduced from thickness of the ambient building applied to $\sigma \cup F'$. -/
theorem link_is_thick (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces) :
    ∀ F' C' : Finset V,
    (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' C' →
    (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C' →
    ∃ D₁ D₂ : Finset V,
      D₁ ≠ C' ∧ D₂ ≠ C' ∧ D₁ ≠ D₂ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' D₁ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D₁ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' D₂ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D₂ := by
  set K := b.toChamberComplex.toSimplicialComplex
  set lk := K.linkComplex σ hσ
  intro F' C' hF'C' hC'_max
  have hF' := hF'C'.1.1
  have hF'_sub_C' := hF'C'.1.2.2
  have hF'_card := hF'C'.2
  have hF'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ F').mp hF'
  have hC'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ C').mp hC'_max.1
  have hσC'_max := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hC'_max
  have h_facet : K.IsFacet (σ ∪ F') (σ ∪ C') := by
    refine ⟨⟨hF'_data.2.2, hC'_data.2.2, Finset.union_subset_union_right hF'_sub_C'⟩, ?_⟩
    rw [SimplicialComplex.sdiff_union_eq_sdiff_of_disjoint' hF'_data.2.1 hC'_data.2.1]
    exact hF'_card
  obtain ⟨D₁, D₂, hD₁_ne, hD₂_ne, hD₁₂_ne, hD₁_facet, hD₁_max, hD₂_facet, hD₂_max⟩ :=
    b.thick (σ ∪ F') (σ ∪ C') h_facet hσC'_max
  have hσD₁ : σ ⊆ D₁ := Finset.subset_union_left.trans hD₁_facet.1.2.2
  have hσD₂ : σ ⊆ D₂ := Finset.subset_union_left.trans hD₂_facet.1.2.2
  have hD₁_ne_σ : (D₁ \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hF'_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hD₁_facet.1.2.2 (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hF'_data.2.1 hv⟩⟩
  have hD₂_ne_σ : (D₂ \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hF'_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hD₂_facet.1.2.2 (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hF'_data.2.1 hv⟩⟩
  have hD₁_link := SimplicialComplex.mem_linkComplex_of_sdiff K σ hσ D₁ hD₁_max.1 hσD₁ hD₁_ne_σ
  have hD₂_link := SimplicialComplex.mem_linkComplex_of_sdiff K σ hσ D₂ hD₂_max.1 hσD₂ hD₂_ne_σ
  have hD₁_eq : σ ∪ (D₁ \ σ) = D₁ := Finset.union_sdiff_of_subset hσD₁
  have hD₂_eq : σ ∪ (D₂ \ σ) = D₂ := Finset.union_sdiff_of_subset hσD₂
  have hD₁_max_K : K.IsMaximal (σ ∪ (D₁ \ σ)) := by rw [hD₁_eq]; exact hD₁_max
  have hD₂_max_K : K.IsMaximal (σ ∪ (D₂ \ σ)) := by rw [hD₂_eq]; exact hD₂_max
  have hD₁_max_lk : lk.IsMaximal (D₁ \ σ) :=
    SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hD₁_link hD₁_max_K
  have hD₂_max_lk : lk.IsMaximal (D₂ \ σ) :=
    SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hD₂_link hD₂_max_K
  have hF'_facet_D₁ : lk.IsFacet F' (D₁ \ σ) := by
    refine ⟨⟨hF', hD₁_link, ?_⟩, ?_⟩
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hD₁_facet.1.2.2 (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hF'_data.2.1 hv⟩
    · have : (D₁ \ σ) \ F' = D₁ \ (σ ∪ F') := by
        ext v; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
      rw [this]; exact hD₁_facet.2
  have hF'_facet_D₂ : lk.IsFacet F' (D₂ \ σ) := by
    refine ⟨⟨hF', hD₂_link, ?_⟩, ?_⟩
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hD₂_facet.1.2.2 (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hF'_data.2.1 hv⟩
    · have : (D₂ \ σ) \ F' = D₂ \ (σ ∪ F') := by
        ext v; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
      rw [this]; exact hD₂_facet.2
  refine ⟨D₁ \ σ, D₂ \ σ, ?_, ?_, ?_,
          hF'_facet_D₁, hD₁_max_lk, hF'_facet_D₂, hD₂_max_lk⟩
  · intro h_eq; apply hD₁_ne
    rw [← hD₁_eq, h_eq]
  · intro h_eq; apply hD₂_ne
    rw [← hD₂_eq, h_eq]
  · intro h_eq; apply hD₁₂_ne
    rw [← hD₁_eq, h_eq, hD₂_eq]

/-- Gallery-connectedness of the link: any two chambers of the link are joined by a gallery,
obtained by transporting a gallery from a common Coxeter link apartment back to the link complex. -/
theorem link_gallery_connected (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C) :
    ∀ C D,
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C →
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D →
      ∃ g : Gallery (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ),
        g.chambers.head? = some C ∧ g.chambers.getLast? = some D := by
  set K := b.toChamberComplex.toSimplicialComplex
  set lk := K.linkComplex σ hσ
  set link_apts : Set (SimplicialComplex V) :=
    {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
      L = A.linkComplex σ hσA}
  intro C D hC_max hD_max

  obtain ⟨L, hL_apt, hC_L, hD_L⟩ :=
    link_contains_pair b σ hσ link_apts rfl C D hC_max hD_max

  obtain ⟨_, _, cc, hcc_eq, _⟩ := link_apt_is_coxeter b σ hσ hσ_proper link_apts rfl L hL_apt

  have hC_max_L : L.IsMaximal C :=
    link_building_maximal_in_apt_is_apt_maximal b σ hσ hσ_proper link_apts rfl L hL_apt C hC_L hC_max
  have hD_max_L : L.IsMaximal D :=
    link_building_maximal_in_apt_is_apt_maximal b σ hσ hσ_proper link_apts rfl L hL_apt D hD_L hD_max

  have hC_max_cc : cc.toSimplicialComplex.IsMaximal C := hcc_eq ▸ hC_max_L
  have hD_max_cc : cc.toSimplicialComplex.IsMaximal D := hcc_eq ▸ hD_max_L
  obtain ⟨g, hg_head, hg_last⟩ := cc.gallery_connected C D hC_max_cc hD_max_cc


  have hL_sub : IsSubcomplex L lk := by
    obtain ⟨A, hA_apt, hσA, rfl⟩ := hL_apt
    exact SimplicialComplex.linkComplex_sub (b.apartmentSystem.sub A hA_apt) σ hσ hσA

  have h_max_lift : ∀ E, L.IsMaximal E → lk.IsMaximal E :=
    fun E hE => link_maximal_in_apt_is_maximal b σ hσ hσ_proper link_apts rfl L hL_apt E hE

  have h_adj_lift : ∀ E F, L.Adjacent E F → lk.Adjacent E F := by
    intro E F ⟨hE_max, hF_max, hne, Fac, hFac_E, hFac_F⟩
    exact ⟨h_max_lift E hE_max, h_max_lift F hF_max, hne, Fac,
      ⟨⟨hL_sub hFac_E.1.1, hL_sub hFac_E.1.2.1, hFac_E.1.2.2⟩, hFac_E.2⟩,
      ⟨⟨hL_sub hFac_F.1.1, hL_sub hFac_F.1.2.1, hFac_F.1.2.2⟩, hFac_F.2⟩⟩

  have h_all_max_lk : ∀ E ∈ g.chambers, lk.IsMaximal E := by
    intro E hE
    exact h_max_lift E (hcc_eq ▸ g.all_maximal E hE)
  have h_chain_lk : List.IsChain lk.Adjacent g.chambers :=
    g.adjacent_consecutive.imp (fun a b hab => h_adj_lift a b (hcc_eq ▸ hab))
  exact ⟨⟨g.chambers, g.length_pos, h_all_max_lk, h_chain_lk⟩, hg_head, hg_last⟩

/-- The *link building*: the link $\mathrm{lk}_K(\sigma)$ of a face $\sigma$ of a building, equipped
with the apartment system consisting of links of ambient apartments, is itself a building. -/
noncomputable def link_building (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C) :
    Building V :=
  let K := b.toChamberComplex.toSimplicialComplex
  let lk := K.linkComplex σ hσ
  let link_apts : Set (SimplicialComplex V) :=
    {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
      L = A.linkComplex σ hσA}
  let link_cc : ChamberComplex V :=
    { toSimplicialComplex := lk
      exists_maximal := link_exists_maximal b σ hσ hσ_proper
      gallery_connected := link_gallery_connected b σ hσ hσ_proper }
  { toChamberComplex := link_cc
    apartmentSystem :=
    { apartments := link_apts
      nonempty_apartments := by
        obtain ⟨A, hA⟩ := b.apartmentSystem.nonempty_apartments
        obtain ⟨C, hC_max, hσ_sub⟩ := hσ_proper
        obtain ⟨B, hB_apt, hC_B, _⟩ := b.apartmentSystem.contains_pair C C hC_max hC_max
        have hσB : σ ∈ B.faces :=
          B.down_closed hC_B hσ_sub.1 (K.nonempty_of_mem σ hσ)
        exact ⟨B.linkComplex σ hσB, B, hB_apt, hσB, rfl⟩
      sub := by
        intro L hL
        obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
        exact SimplicialComplex.linkComplex_sub (b.apartmentSystem.sub A hA_apt) σ hσ hσA
      contains_pair := by
        intro C' D' hC'_max hD'_max
        exact link_contains_pair b σ hσ link_apts rfl C' D' hC'_max hD'_max
      iso_exists := link_iso_exists b σ hσ hσ_proper link_apts rfl
      maximal_in_apt_is_maximal :=
        link_maximal_in_apt_is_maximal b σ hσ hσ_proper link_apts rfl
      gallery_convex :=
        link_gallery_convex b σ hσ hσ_proper link_cc rfl link_apts rfl
      building_maximal_in_apt_is_apt_maximal :=
        link_building_maximal_in_apt_is_apt_maximal b σ hσ hσ_proper link_apts rfl
      apt_nonempty := link_apt_nonempty b σ hσ hσ_proper link_apts rfl
      iso_bijective := link_iso_bijective b σ hσ hσ_proper link_apts rfl
      apt_is_coxeter := link_apt_is_coxeter b σ hσ hσ_proper link_apts rfl }
    thick := by
      intro F' C' hF'C' hC'_max
      exact link_is_thick b σ hσ F' C' hF'C' hC'_max }

end Building
