import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.RetractionDef
import sympy.atlas.v1.Atlas.Buildings.code.Building.Convexity
import Lemma.List.Any.of.Not.In_A.IsChainA
open scoped Classical


/--
[galleryDist_le_of_gallery](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/RetractionProperties.lean)
-/
@[path]
lemma galleryDist_le_of_gallery
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C D : Finset V}
  {g : Gallery K}
-- given
  (hconn : g.Connects C D) :
-- imply
  galleryDist K C D ≤ g.length := by
-- proof
  by_cases hCD : C = D
  · subst hCD; simp [galleryDist_self]
  · unfold galleryDist
    rw [if_neg hCD]
    apply Nat.sInf_le
    exact ⟨g, hconn, rfl⟩

private lemma exists_retraction_gallery
  [DecidableEq V]
  {b : Building V}
  {ρ : BuildingRetraction b}
  {L : List (Finset V)}
-- given
  (hne : L ≠ [])
  (hmax : ∀ C ∈ L, b.toChamberComplex.toSimplicialComplex.IsMaximal C)
  (hchain : List.IsChain b.toChamberComplex.toSimplicialComplex.Adjacent L) :
-- imply
  ∃ g : Gallery ρ.apt, g.Connects (Finset.image ρ.map (L.head hne)) (Finset.image ρ.map (L.getLast hne)) ∧ g.length ≤ L.length - 1 := by
-- proof
  induction L with
  | nil => exact absurd rfl hne
  | cons c₁ tail ih =>
    cases tail with
    | nil =>
      have hc₁_max := hmax c₁ (by simp)
      refine ⟨⟨[Finset.image ρ.map c₁], by simp, ?_, List.isChain_singleton _⟩, ?_, ?_⟩
      · intro C hC; simp at hC; exact hC ▸ ρ.map_chamber c₁ hc₁_max
      · exact ⟨rfl, rfl⟩
      · simp [Gallery.length]
    | cons c₂ rest =>
      have htail_ne : (c₂ :: rest) ≠ [] := List.cons_ne_nil _ _
      have htail_max : ∀ C ∈ (c₂ :: rest),
        b.toChamberComplex.toSimplicialComplex.IsMaximal C :=
        fun C hC => hmax C (List.mem_cons_of_mem c₁ hC)
      have htail_chain :
        List.IsChain b.toChamberComplex.toSimplicialComplex.Adjacent (c₂ :: rest) :=
        hchain.tail
      obtain ⟨g_tail, hg_conn, hg_len⟩ := ih htail_ne htail_max htail_chain
      have hadj_X : b.toChamberComplex.toSimplicialComplex.Adjacent c₁ c₂ :=
        hchain.rel_head
      have h_or := ρ.map_adj_or_eq c₁ c₂ hadj_X
      cases h_or with
      | inl heq =>
        refine ⟨g_tail, ?_, ?_⟩
        · constructor
          ·
            have h1 := hg_conn.1
            simp only [List.head_cons] at h1 ⊢
            rwa [heq]
          ·
            have h2 := hg_conn.2
            simp only [List.getLast_cons (by exact htail_ne)] at h2 ⊢
            exact h2
        ·
          calc g_tail.length ≤ (c₂ :: rest).length - 1 := hg_len
            _ ≤ (c₁ :: c₂ :: rest).length - 1 := by simp
      | inr hadj_A =>
        have hne_gtail := List.ne_nil_of_length_pos g_tail.length_pos
        have h_head_gtail : g_tail.chambers.head hne_gtail =
          Finset.image ρ.map c₂ := by
          have h1 := hg_conn.1
          simp [List.head?_eq_head hne_gtail] at h1
          exact h1
        have hc₁_max := hmax c₁ (by simp)
        refine ⟨{
          chambers := Finset.image ρ.map c₁ :: g_tail.chambers
          length_pos := by simp
          all_maximal := by
            intro C hC; simp at hC
            cases hC with
            | inl h => exact h ▸ ρ.map_chamber c₁ hc₁_max
            | inr h => exact g_tail.all_maximal C h
          adjacent_consecutive := by
            apply g_tail.adjacent_consecutive.cons
            intro y hy
            rw [List.head?_eq_head hne_gtail] at hy
            simp at hy; subst hy
            rwa [h_head_gtail]
        }, ?_, ?_⟩
        ·
          constructor
          · simp [Gallery.Connects]
          ·
            simp [Gallery.Connects]
            rw [List.getLast?_eq_getLast (by simp [hne_gtail] : (Finset.image ρ.map c₁ :: g_tail.chambers) ≠ [])]
            simp [List.getLast_cons (show g_tail.chambers ≠ [] from hne_gtail)]
            have h2 := hg_conn.2
            rw [List.getLast?_eq_getLast hne_gtail] at h2
            simp at h2
            rw [h2]
        ·
          simp only [Gallery.length, List.length_cons]
          have hlen1 : g_tail.chambers.length ≥ 1 := g_tail.length_pos
          simp [Gallery.length] at hg_len
          omega

private lemma retraction_image_gallery_bound
  [DecidableEq V]
  {b : Building V}
  {ρ : BuildingRetraction b}
  {g : Gallery b.toChamberComplex.toSimplicialComplex}
  {C D : Finset V}
-- given
  (hconn : g.Connects C D) :
-- imply
  galleryDist ρ.apt (C.image ρ.map) (D.image ρ.map) ≤ g.length := by
-- proof
  have hne := List.ne_nil_of_length_pos g.length_pos
  have hC : C = g.chambers.head hne := by
    have := hconn.1; simp [List.head?_eq_head hne] at this; exact this.symm
  have hD : D = g.chambers.getLast hne := by
    have := hconn.2; simp [List.getLast?_eq_getLast hne] at this; exact this.symm
  rw [hC, hD]
  obtain ⟨g', hg'_conn, hg'_len⟩ := exists_retraction_gallery ρ g.chambers hne
    g.all_maximal g.adjacent_consecutive
  calc galleryDist ρ.apt _ _ ≤ g'.length := galleryDist_le_of_gallery g' hg'_conn
    _ ≤ g.chambers.length - 1 := hg'_len
    _ = g.length := rfl

private lemma BuildingRetraction.isDistanceDiminishing
  [DecidableEq V]
  {b : Building V}
  {ρ : BuildingRetraction b} :
-- imply
  ρ.IsDistanceDiminishing := by
-- proof
  intro C D hC hD
  by_cases hCD : C = D
  · subst hCD; simp [galleryDist_self]
  · unfold galleryDist
    rw [if_neg hCD]
    by_cases heq : C.image ρ.map = D.image ρ.map
    · rw [heq]; simp
    · apply le_csInf
      · obtain ⟨g, hg⟩ := b.toChamberComplex.gallery_connected C D hC hD
        exact ⟨g.length, g, ⟨hg.1, hg.2⟩, rfl⟩
      · intro n hn
        obtain ⟨g, hconn, hlen⟩ := hn
        rw [← hlen]
        exact retraction_image_gallery_bound ρ g hconn


-- created on 2026-10-24
