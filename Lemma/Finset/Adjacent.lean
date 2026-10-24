import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Basic


/--
[SimplicialComplex.adjacent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Basic.lean)
-/
@[path]
lemma SimplicialComplex.adjacent_symm
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C D : Finset V} :
-- imply
  K.Adjacent C D → K.Adjacent D C := by
-- proof
  intro ⟨hC, hD, hne, F, hFC, hFD⟩
  exact ⟨hD, hC, hne.symm, F, hFD, hFC⟩

private lemma galleryDist_comm
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C D : Finset V} :
-- imply
  galleryDist K C D = galleryDist K D C := by
-- proof
  unfold galleryDist
  by_cases hCD : C = D
  · subst hCD; simp
  · have hDC : D ≠ C := hCD ∘ Eq.symm
    simp [hCD, hDC, ite_false]
    congr 1
    ext n
    constructor
    · rintro ⟨g, hconn, hlen⟩
      have hrev_len : g.chambers.reverse.length > 0 := by
        simp [g.length_pos]
      have hrev_max : ∀ E ∈ g.chambers.reverse, K.IsMaximal E := by
        intro E hE
        exact g.all_maximal E (List.mem_reverse.mp hE)
      have hrev_chain : List.IsChain K.Adjacent g.chambers.reverse := by
        rw [List.isChain_reverse]
        exact g.adjacent_consecutive.imp (fun _ _ h => K.adjacent_symm _ _ h)
      refine ⟨⟨g.chambers.reverse, hrev_len, hrev_max, hrev_chain⟩, ?_, ?_⟩
      · constructor
        · rw [List.head?_reverse]
          exact hconn.2
        · rw [List.getLast?_reverse]
          exact hconn.1
      · simp [Gallery.length, List.length_reverse]; exact hlen
    · rintro ⟨g, hconn, hlen⟩
      have hrev_len : g.chambers.reverse.length > 0 := by
        simp [g.length_pos]
      have hrev_max : ∀ E ∈ g.chambers.reverse, K.IsMaximal E := by
        intro E hE
        exact g.all_maximal E (List.mem_reverse.mp hE)
      have hrev_chain : List.IsChain K.Adjacent g.chambers.reverse := by
        rw [List.isChain_reverse]
        exact g.adjacent_consecutive.imp (fun _ _ h => K.adjacent_symm _ _ h)
      refine ⟨⟨g.chambers.reverse, hrev_len, hrev_max, hrev_chain⟩, ?_, ?_⟩
      · constructor
        · rw [List.head?_reverse]
          exact hconn.2
        · rw [List.getLast?_reverse]
          exact hconn.1
      · simp [Gallery.length, List.length_reverse]; exact hlen

private lemma galleryDist_self_eq
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C : Finset V} :
-- imply
  galleryDist K C C = 0 := by
-- proof
  apply galleryDist_self K C


-- created on 2026-10-24
