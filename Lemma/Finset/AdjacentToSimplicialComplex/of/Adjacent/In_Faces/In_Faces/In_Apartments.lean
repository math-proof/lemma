import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery
open CombinatorialGeometry
open scoped Classical


/--
[apt_adj_lifts_to_bldg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/PrescribedGallery.lean)
-/
@[path]
lemma apt_adj_lifts_to_bldg
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (_hC : C ∈ A.faces)
  (_hD : D ∈ A.faces)
  (hadj : A.Adjacent C D) :
-- imply
  b.toSimplicialComplex.Adjacent C D := by
-- proof
  obtain ⟨hCmax_A, hDmax_A, hne, F, hFC, hFD⟩ := hadj
  have hCmax_bldg := b.apartmentSystem.maximal_in_apt_is_maximal A hA C hCmax_A
  have hDmax_bldg := b.apartmentSystem.maximal_in_apt_is_maximal A hA D hDmax_A
  have hFC_bldg : b.toSimplicialComplex.IsFacet F C :=
    ⟨⟨b.apartmentSystem.sub A hA hFC.1.1,
      b.apartmentSystem.sub A hA hFC.1.2.1, hFC.1.2.2⟩, hFC.2⟩
  have hFD_bldg : b.toSimplicialComplex.IsFacet F D :=
    ⟨⟨b.apartmentSystem.sub A hA hFD.1.1,
      b.apartmentSystem.sub A hA hFD.1.2.1, hFD.1.2.2⟩, hFD.2⟩
  exact ⟨hCmax_bldg, hDmax_bldg, hne, F, hFC_bldg, hFD_bldg⟩


private lemma apt_chain_of_length
  [DecidableEq V]
  {A : SimplicialComplex V}
  {C : Finset V}
  {n : ℕ}
-- given
  (h_has_adj : ∀ C, A.IsMaximal C → ∃ D, A.Adjacent C D)
  (hC : C ∈ A.faces)
  (hCmax : A.IsMaximal C) :
-- imply
  ∃ (cs : List (Finset V)), cs.head? = some C ∧ cs.length = n + 1 ∧ (∀ E ∈ cs, E ∈ A.faces) ∧ List.IsChain A.Adjacent cs := by
-- proof
  induction n generalizing C with
  | zero =>
    exact ⟨[C], rfl, rfl,
      fun E hE => by simp at hE; rw [hE]; exact hC,
      List.IsChain.singleton C⟩
  | succ n ih =>
    obtain ⟨D, hAdj_CD⟩ := h_has_adj C hCmax
    have hDmax : A.IsMaximal D := hAdj_CD.2.1
    have hD : D ∈ A.faces := hDmax.1
    obtain ⟨cs_tail, hhead_tail, hlen_tail, hmem_tail, hchain_tail⟩ :=
      ih D hD hDmax
    refine ⟨C :: cs_tail, rfl, ?_, ?_, ?_⟩
    ·
      simp [hlen_tail]
    ·
      intro E hE
      simp only [List.mem_cons] at hE
      obtain rfl | hE := hE
      · exact hC
      · exact hmem_tail E hE
    ·
      cases cs_tail with
      | nil => simp at hlen_tail
      | cons D' rest =>
        simp at hhead_tail
        rw [hhead_tail] at hchain_tail ⊢
        exact List.IsChain.cons_cons hAdj_CD hchain_tail


private lemma mk_prescribed_gallery_hyp
  [DecidableEq V]
  {b : Building V}
-- given
  (h_apt_has_adj : ∀ A ∈ b.apartmentSystem.apartments, ∀ C, A.IsMaximal C → ∃ D, A.Adjacent C D) :
-- imply
  PrescribedGalleryHypotheses b where apt_gallery_of_type := by
-- proof
  intro A hA C hC hCmax τ
  exact apt_chain_of_length A (h_apt_has_adj A hA) C hC hCmax τ.length
  apt_adj_implies_bldg_adj := by
    intro A hA C D hC hD hadj
    exact apt_adj_lifts_to_bldg b A hA C D hC hD hadj


-- created on 2026-10-24
