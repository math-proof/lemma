import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
open SimplicialComplex
open scoped Classical


/--
[agreeOn_imp_agreeOnImage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Uniqueness.lean)
-/
@[path]
lemma agreeOn_imp_agreeOnImage
  [DecidableEq V]
  [DecidableEq W]
  {K : SimplicialComplex V}
  {L : SimplicialComplex W}
  {f g : Morphism K L}
  {C : Finset V}
-- given
  (h : AgreeOn f g C) :
-- imply
  AgreeOnImage f g C := by
-- proof
  unfold AgreeOnImage
  apply Finset.image_congr
  intro x hx
  exact h x hx


private lemma agree_image_next_chamber
  [DecidableEq V]
  [DecidableEq W]
  {K : SimplicialComplex V}
  {L : SimplicialComplex W}
  {f g : Morphism K L}
  {C₁ C₂ : Finset V}
-- given
  (hL : AtMostTwoChambers L)
  (hf : f.IsChamberMap)
  (hg : g.IsChamberMap)
  (hfF : f.PreservesFacets)
  (hgF : g.PreservesFacets)
  (hf_ns : f.NonStutteringAdj)
  (hg_ns : g.NonStutteringAdj)
  (hcompat : SubFaceCompatible f g)
  (hadj : K.Adjacent C₁ C₂)
  (hC₁_max : K.IsMaximal C₁)
  (hagree : AgreeOnImage f g C₁) :
-- imply
  AgreeOnImage f g C₂ := by
-- proof
  have hadj' := hadj
  obtain ⟨_, hC₂, _, F, hFC₁, hFC₂⟩ := hadj'
  have hFimg : AgreeOnImage f g F := hcompat C₁ hC₁_max hagree F hFC₁.1
  have hfFC₂ : L.IsFacet (F.image f.toFun) (C₂.image f.toFun) := hfF F C₂ hFC₂
  have hgFC₂ : L.IsFacet (F.image f.toFun) (C₂.image g.toFun) :=
    hFimg ▸ hgF F C₂ hFC₂
  have hfFC₁ : L.IsFacet (F.image f.toFun) (C₁.image f.toFun) := hfF F C₁ hFC₁
  have hfC₁_max : L.IsMaximal (C₁.image f.toFun) := hf C₁ hC₁_max
  have hfC₂_max : L.IsMaximal (C₂.image f.toFun) := hf C₂ hC₂
  have hgC₂_max : L.IsMaximal (C₂.image g.toFun) := hg C₂ hC₂
  have hf_ne : C₁.image f.toFun ≠ C₂.image f.toFun := hf_ns C₁ C₂ hadj
  have hg_ne : C₁.image f.toFun ≠ C₂.image g.toFun := hagree ▸ hg_ns C₁ C₂ hadj
  exact hL (F.image f.toFun) (C₁.image f.toFun) (C₂.image f.toFun) (C₂.image g.toFun)
    hfFC₁ hfC₁_max hfFC₂ hfC₂_max (Ne.symm hf_ne) hgFC₂ hgC₂_max (Ne.symm hg_ne)
set_option linter.unusedSectionVars false in


variable {V W : Type*} [DecidableEq V] [DecidableEq W]

private lemma mem_of_getLast?_eq_some {α : Type*} {l : List α} {a : α}
  (h : l.getLast? = some a) : a ∈ l := by
  rw [List.getLast?_eq_some_iff] at h
  obtain ⟨ys, rfl⟩ := h
  simp


private lemma agree_image_along_chain
  [DecidableEq V]
  [DecidableEq W]
  {K : SimplicialComplex V}
  {L : SimplicialComplex W}
  {f g : Morphism K L}
  {cs : List (Finset V)}
-- given
  (hL : AtMostTwoChambers L)
  (hf : f.IsChamberMap)
  (hg : g.IsChamberMap)
  (hfF : f.PreservesFacets)
  (hgF : g.PreservesFacets)
  (hf_ns : f.NonStutteringAdj)
  (hg_ns : g.NonStutteringAdj)
  (hcompat : SubFaceCompatible f g)
  (hne : cs ≠ [])
  (hchain : List.IsChain K.Adjacent cs)
  (hall : ∀ C ∈ cs, K.IsMaximal C)
  (hagree : AgreeOnImage f g (cs.head hne)) :
-- imply
  ∀ D ∈ cs, AgreeOnImage f g D := by
-- proof
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro D hD
    rw [List.mem_cons] at hD
    obtain rfl | hD := hD
    · exact hagree
    · cases tl with
      | nil => simp at hD
      | cons b rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : K.Adjacent a b := hrel b rfl
        have ha_max : K.IsMaximal a := hall a (List.mem_cons_self)
        have hagree_b : AgreeOnImage f g b :=
          agree_image_next_chamber hL f g hf hg hfF hgF hf_ns hg_ns hcompat
            hab ha_max hagree
        exact ih (List.cons_ne_nil b rest) hchain_tl
          (fun C hC => hall C (List.mem_cons_of_mem a hC))
          hagree_b D hD


private lemma uniqueness_lemma_32
  [DecidableEq V]
  [DecidableEq W]
  {K : ChamberComplex V}
  {L : SimplicialComplex W}
  {f g : Morphism K.toSimplicialComplex L}
  {C : Finset V}
-- given
  (hL : AtMostTwoChambers L)
  (hf : f.IsChamberMap)
  (hg : g.IsChamberMap)
  (hfF : f.PreservesFacets)
  (hgF : g.PreservesFacets)
  (hf_ns : f.NonStutteringAdj)
  (hg_ns : g.NonStutteringAdj)
  (hcompat : SubFaceCompatible f g)
  (hC : K.toSimplicialComplex.IsMaximal C)
  (hagree : AgreeOnImage f g C) :
-- imply
  ∀ D, K.toSimplicialComplex.IsMaximal D → AgreeOnImage f g D := by
-- proof
  intro D hD
  obtain ⟨gal, hgal_head, hgal_last⟩ := K.gallery_connected C D hC hD
  have hD_mem : D ∈ gal.chambers := mem_of_getLast?_eq_some hgal_last
  have hne : gal.chambers ≠ [] := by
    intro h; simp [h] at hgal_head
  have hhead_eq : gal.chambers.head hne = C := by
    rw [List.head?_eq_some_head hne] at hgal_head
    exact Option.some_injective _ hgal_head
  exact agree_image_along_chain hL f g hf hg hfF hgF hf_ns hg_ns hcompat
    gal.chambers hne gal.adjacent_consecutive gal.all_maximal
    (hhead_eq ▸ hagree) D hD_mem


private lemma image_eq_of_fixes_pointwise
  [DecidableEq V]
  [DecidableEq W]
  {f : V → V}
  {C : Finset V}
-- given
  (h : ∀ v ∈ C, f v = v) :
-- imply
  C.image f = C := by
-- proof
  ext x; simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [h y hy]
  · intro hx; exact ⟨x, hx, h x hx⟩


private lemma fixes_pointwise_of_facet_and_image
  [DecidableEq V]
  [DecidableEq W]
  {f : V → V}
  {C F : Finset V}
-- given
  (hFC : F ⊆ C)
  (hcard : (C \ F).card = 1)
  (hfixF : ∀ v ∈ F, f v = v)
  (himg : C.image f = C) :
-- imply
  ∀ v ∈ C, f v = v := by
-- proof
  intro v hv
  by_cases hvF : v ∈ F
  · exact hfixF v hvF
  · have hv_diff : v ∈ C \ F := Finset.mem_sdiff.mpr ⟨hv, hvF⟩
    have hsingleton : C \ F = {v} := by
      rw [Finset.card_eq_one] at hcard
      obtain ⟨w, hw⟩ := hcard
      have : v = w := by rw [hw] at hv_diff; simp at hv_diff; exact hv_diff
      rw [this]; exact hw
    have hC_eq : C = F ∪ {v} := by
      ext x; constructor
      · intro hx
        simp only [Finset.mem_union, Finset.mem_singleton]
        by_cases hxF : x ∈ F
        · left; exact hxF
        · right
          have : x ∈ C \ F := Finset.mem_sdiff.mpr ⟨hx, hxF⟩
          rw [hsingleton] at this; simp at this; exact this
      · simp only [Finset.mem_union, Finset.mem_singleton]
        rintro (hx | rfl)
        · exact hFC hx
        · exact hv
    rw [hC_eq, Finset.image_union, Finset.image_singleton] at himg
    have hFimg : F.image f = F := image_eq_of_fixes_pointwise hfixF
    rw [hFimg] at himg
    have hv_mem : v ∈ F ∪ {f v} := by rw [himg]; simp
    simp only [Finset.mem_union, Finset.mem_singleton] at hv_mem
    exact hv_mem.elim (fun h => absurd h hvF) Eq.symm


private lemma thin_fixes_next_chamber
  [DecidableEq V]
  [DecidableEq W]
  {X : ChamberComplex V}
  {f : Morphism X.toSimplicialComplex X.toSimplicialComplex}
  {C₁ C₂ : Finset V}
-- given
  (hthin : X.IsThin)
  (hf : f.IsChamberMap)
  (hfF : f.PreservesFacets)
  (hadj : X.toSimplicialComplex.Adjacent C₁ C₂)
  (hfix₁ : ∀ v ∈ C₁, f.toFun v = v)
  (hne : C₂.image f.toFun ≠ C₁) :
-- imply
  ∀ v ∈ C₂, f.toFun v = v := by
-- proof
  obtain ⟨hC₁max, hC₂max, hC₁C₂, F, hFC₁, hFC₂⟩ := hadj
  have hF_sub_C₁ : F ⊆ C₁ := hFC₁.1.2.2
  have hfixF : ∀ v ∈ F, f.toFun v = v := fun v hv => hfix₁ v (hF_sub_C₁ hv)
  have hFimg : F.image f.toFun = F := image_eq_of_fixes_pointwise hfixF
  have hfacet : X.toSimplicialComplex.IsFacet (F.image f.toFun) (C₂.image f.toFun) :=
    hfF F C₂ hFC₂
  rw [hFimg] at hfacet
  have hfC₂max : X.toSimplicialComplex.IsMaximal (C₂.image f.toFun) := hf C₂ hC₂max
  have hthin_inst := hthin F C₁ hFC₁ hC₁max
  obtain ⟨D, ⟨hDC₁, hFD, hDmax⟩, huniq⟩ := hthin_inst
  have hC₂_eq_D : C₂ = D := huniq C₂ ⟨hC₁C₂.symm, hFC₂, hC₂max⟩
  have hfC₂_eq_D : C₂.image f.toFun = D :=
    huniq (C₂.image f.toFun) ⟨hne, hfacet, hfC₂max⟩
  have hC₂img : C₂.image f.toFun = C₂ := by rw [hfC₂_eq_D, ← hC₂_eq_D]
  exact fixes_pointwise_of_facet_and_image hFC₂.1.2.2 hFC₂.2 hfixF hC₂img


private lemma fixes_along_chain_of_nonstuttering
  [DecidableEq V]
  [DecidableEq W]
  {X : ChamberComplex V}
  {f : Morphism X.toSimplicialComplex X.toSimplicialComplex}
  {cs : List (Finset V)}
-- given
  (hthin : X.IsThin)
  (hf : f.IsChamberMap)
  (hfF : f.PreservesFacets)
  (hne : cs ≠ [])
  (hchain : List.IsChain X.toSimplicialComplex.Adjacent cs)
  (hall : ∀ C ∈ cs, X.toSimplicialComplex.IsMaximal C)
  (hfix_head : ∀ v ∈ cs.head hne, f.toFun v = v)
  (hns : List.IsChain (· ≠ ·) (cs.map (fun C => C.image f.toFun))) :
-- imply
  ∀ C ∈ cs, ∀ v ∈ C, f.toFun v = v := by
-- proof
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro C hC
    rw [List.mem_cons] at hC
    obtain rfl | hC := hC
    · exact hfix_head
    · cases tl with
      | nil => simp at hC
      | cons b rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : X.toSimplicialComplex.Adjacent a b := hrel b rfl
        have hns_cons : List.IsChain (· ≠ ·)
          ((a.image f.toFun) :: (b :: rest).map (fun C => C.image f.toFun)) := hns
        rw [List.isChain_cons] at hns_cons
        obtain ⟨hrel_ns, hns_tl⟩ := hns_cons
        have hab_ns : a.image f.toFun ≠ b.image f.toFun := by
          have := hrel_ns (b.image f.toFun) rfl
          exact this
        have ha_img : a.image f.toFun = a := image_eq_of_fixes_pointwise hfix_head
        have hne_ba : b.image f.toFun ≠ a := by rw [← ha_img]; exact hab_ns.symm
        have hfix_b : ∀ v ∈ b, f.toFun v = v :=
          thin_fixes_next_chamber hthin f hf hfF hab hfix_head hne_ba
        exact ih (List.cons_ne_nil b rest) hchain_tl
          (fun D hD => hall D (List.mem_cons_of_mem a hD))
          hfix_b hns_tl C hC


private lemma uniqueness_lemma_book
  [DecidableEq V]
  [DecidableEq W]
  {X : ChamberComplex V}
  {f : Morphism X.toSimplicialComplex X.toSimplicialComplex}
  {C₀ : Finset V}
  {γ : Gallery X.toSimplicialComplex}
-- given
  (hthin : X.IsThin)
  (hf : f.IsChamberMap)
  (hfF : f.PreservesFacets)
  (_hC₀ : X.toSimplicialComplex.IsMaximal C₀)
  (hfix : ∀ v ∈ C₀, f.toFun v = v)
  (hstart : γ.chambers.head? = some C₀) :
-- imply
  GalleryStuttersUnder γ.chambers f.toFun ∨ FixesAllPointwise γ.chambers f.toFun := by
-- proof
  by_cases hns : List.IsChain (· ≠ ·) (γ.chambers.map (fun C => C.image f.toFun))
  ·
    right
    have hne : γ.chambers ≠ [] := by
      intro h; simp [h] at hstart
    have hhead_eq : γ.chambers.head hne = C₀ := by
      rw [List.head?_eq_some_head hne] at hstart
      exact Option.some_injective _ hstart
    intro C hC v hv
    exact fixes_along_chain_of_nonstuttering hthin f hf hfF
      γ.chambers hne γ.adjacent_consecutive γ.all_maximal
      (hhead_eq ▸ hfix) hns C hC v hv
  ·
    left
    exact hns


private lemma thin_fixes_next_chamber_no_pfacets
  [DecidableEq V]
  [DecidableEq W]
  {X : ChamberComplex V}
  {f : Morphism X.toSimplicialComplex X.toSimplicialComplex}
  {C₁ C₂ : Finset V}
-- given
  (hthin : X.IsThin)
  (hf : f.IsChamberMap)
  (hadj : X.toSimplicialComplex.Adjacent C₁ C₂)
  (hfix₁ : ∀ v ∈ C₁, f.toFun v = v)
  (hne : C₂.image f.toFun ≠ C₁) :
-- imply
  ∀ v ∈ C₂, f.toFun v = v := by
-- proof
  obtain ⟨hC₁max, hC₂max, hC₁C₂, F, hFC₁, hFC₂⟩ := hadj
  have hF_sub_C₁ : F ⊆ C₁ := hFC₁.1.2.2
  have hfixF : ∀ v ∈ F, f.toFun v = v := fun v hv => hfix₁ v (hF_sub_C₁ hv)
  have hF_sub_C₂ : F ⊆ C₂ := hFC₂.1.2.2
  have hF_sub_fC₂ : F ⊆ C₂.image f.toFun := by
    intro v hv
    simp only [Finset.mem_image]
    exact ⟨v, hF_sub_C₂ hv, hfixF v hv⟩
  have hfC₂max : X.toSimplicialComplex.IsMaximal (C₂.image f.toFun) := hf C₂ hC₂max
  have hfC₂_facet : X.toSimplicialComplex.IsFacet F (C₂.image f.toFun) := by
    constructor
    · exact ⟨hFC₁.1.1, hfC₂max.1, hF_sub_fC₂⟩
    ·
      have h1 : (C₂ \ F).card = 1 := hFC₂.2
      have h2 : C₂.card = F.card + 1 := by
        have := Finset.card_sdiff_add_card_eq_card hF_sub_C₂; omega
      have h3 : (C₂.image f.toFun).card ≤ C₂.card := Finset.card_image_le
      have h4 : F.card ≤ (C₂.image f.toFun).card := Finset.card_le_card hF_sub_fC₂
      have h5 : (C₂.image f.toFun).card = F.card ∨
        (C₂.image f.toFun).card = F.card + 1 := by omega
      obtain h5 | h5 := h5
      ·
        exfalso
        have hfC₂_eq_F : C₂.image f.toFun = F :=
          (Finset.eq_of_subset_of_card_le hF_sub_fC₂ (by omega)).symm
        rw [hfC₂_eq_F] at hfC₂max
        have hF_ne_C₁ : F ≠ C₁ := by
          intro heq; rw [heq] at hFC₁
          have : (C₁ \ C₁).card = 1 := hFC₁.2
          simp at this
        exact hF_ne_C₁ (hfC₂max.2 C₁ hC₁max.1 hF_sub_C₁)
      ·
        have := Finset.card_sdiff_add_card_eq_card hF_sub_fC₂; omega
  have hthin_inst := hthin F C₁ hFC₁ hC₁max
  obtain ⟨D, ⟨hDC₁, hFD, hDmax⟩, huniq⟩ := hthin_inst
  have hC₂_eq_D : C₂ = D := huniq C₂ ⟨hC₁C₂.symm, hFC₂, hC₂max⟩
  have hfC₂_eq_D : C₂.image f.toFun = D :=
    huniq (C₂.image f.toFun) ⟨hne, hfC₂_facet, hfC₂max⟩
  have hC₂img : C₂.image f.toFun = C₂ := by rw [hfC₂_eq_D, ← hC₂_eq_D]
  exact fixes_pointwise_of_facet_and_image hFC₂.1.2.2 hFC₂.2 hfixF hC₂img


private lemma fixes_along_chain_no_pfacets
  [DecidableEq V]
  [DecidableEq W]
  {X : ChamberComplex V}
  {f : Morphism X.toSimplicialComplex X.toSimplicialComplex}
  {cs : List (Finset V)}
-- given
  (hthin : X.IsThin)
  (hf : f.IsChamberMap)
  (hne : cs ≠ [])
  (hchain : List.IsChain X.toSimplicialComplex.Adjacent cs)
  (hall : ∀ C ∈ cs, X.toSimplicialComplex.IsMaximal C)
  (hfix_head : ∀ v ∈ cs.head hne, f.toFun v = v)
  (hns : List.IsChain (· ≠ ·) (cs.map (fun C => C.image f.toFun))) :
-- imply
  ∀ C ∈ cs, ∀ v ∈ C, f.toFun v = v := by
-- proof
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro C hC
    rw [List.mem_cons] at hC
    obtain rfl | hC := hC
    · exact hfix_head
    · cases tl with
      | nil => simp at hC
      | cons b rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : X.toSimplicialComplex.Adjacent a b := hrel b rfl
        have hns_cons : List.IsChain (· ≠ ·)
          ((a.image f.toFun) :: (b :: rest).map (fun C => C.image f.toFun)) := hns
        rw [List.isChain_cons] at hns_cons
        obtain ⟨hrel_ns, hns_tl⟩ := hns_cons
        have hab_ns : a.image f.toFun ≠ b.image f.toFun := by
          have := hrel_ns (b.image f.toFun) rfl
          exact this
        have ha_img : a.image f.toFun = a := image_eq_of_fixes_pointwise hfix_head
        have hne_ba : b.image f.toFun ≠ a := by rw [← ha_img]; exact hab_ns.symm
        have hfix_b : ∀ v ∈ b, f.toFun v = v :=
          thin_fixes_next_chamber_no_pfacets hthin f hf hab hfix_head hne_ba
        exact ih (List.cons_ne_nil b rest) hchain_tl
          (fun D hD => hall D (List.mem_cons_of_mem a hD))
          hfix_b hns_tl C hC


private lemma uniqueness_lemma
  [DecidableEq V]
  [DecidableEq W]
  {X : ChamberComplex V}
  {f : Morphism X.toSimplicialComplex X.toSimplicialComplex}
  {C₀ : Finset V}
  {γ : Gallery X.toSimplicialComplex}
-- given
  (hthin : X.IsThin)
  (hf : f.IsChamberMap)
  (_hC₀ : X.toSimplicialComplex.IsMaximal C₀)
  (hfix : ∀ v ∈ C₀, f.toFun v = v)
  (hstart : γ.chambers.head? = some C₀) :
-- imply
  GalleryStuttersUnder γ.chambers f.toFun ∨ FixesAllPointwise γ.chambers f.toFun := by
-- proof
  by_cases hns : List.IsChain (· ≠ ·) (γ.chambers.map (fun C => C.image f.toFun))
  ·
    right
    have hne : γ.chambers ≠ [] := by
      intro h; simp [h] at hstart
    have hhead_eq : γ.chambers.head hne = C₀ := by
      rw [List.head?_eq_some_head hne] at hstart
      exact Option.some_injective _ hstart
    intro C hC v hv
    exact fixes_along_chain_no_pfacets hthin f hf
      γ.chambers hne γ.adjacent_consecutive γ.all_maximal
      (hhead_eq ▸ hfix) hns C hC v hv
  ·
    left
    exact hns


private lemma mem_of_getLast_eq
  [DecidableEq V]
  [DecidableEq W]
  {l : List α}
  {a : α}
-- given
  (h : l.getLast? = some a) :
-- imply
  a ∈ l := by
-- proof
  apply SimplicialComplex.mem_of_getLast h


-- created on 2026-10-24
