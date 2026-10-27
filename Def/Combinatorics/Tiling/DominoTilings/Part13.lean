import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part10
open Finset BigOperators


namespace DominoTilings

noncomputable def reflectTiling3 {n : ℕ} (T : DominoTiling n 3) : DominoTiling n 3 where
  dominos := T.dominos.attach.map ⟨fun ⟨d, hd⟩ =>
    reflectDomino3 d
      (domino_cell1_row_le' (T.dominos_in_rect d hd))
      (domino_cell2_row_le' (T.dominos_in_rect d hd)),
    by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only [Subtype.mk.injEq]
      exact reflectDomino3_injective _ _ _ _ hab⟩
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    exact reflectDomino3_cells_subset (T.dominos_in_rect d' hd') _ _
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_attach, true_and,
        Subtype.exists, ← Function.Embedding.toFun_eq_coe] at hc
      obtain ⟨d, ⟨d', hd', rfl⟩, hc_in_d⟩ := hc
      rw [reflectDomino3_cells] at hc_in_d
      simp only [Finset.mem_image] at hc_in_d
      obtain ⟨c', hc', rfl⟩ := hc_in_d
      have hc'_rect : c' ∈ Rectangle n 3 := T.dominos_in_rect d' hd' hc'
      exact reflectCell3_mem_Rectangle' hc'_rect
    · intro hc
      -- c is in Rectangle n 3, need to show it's covered by some reflected domino
      -- Find c' such that reflectCell3 c' = c
      obtain ⟨c', hc'_rect, hc'_eq⟩ := reflectCell3_surjective_on_rect hc
      -- c' is covered by some domino d' in T
      rw [← T.covers_all] at hc'_rect
      simp only [Finset.mem_biUnion] at hc'_rect
      obtain ⟨d', hd', hc'_in_d'⟩ := hc'_rect
      -- The reflected domino covers c
      simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_attach, true_and,
        Subtype.exists, ← Function.Embedding.toFun_eq_coe]
      use reflectDomino3 d' (domino_cell1_row_le' (T.dominos_in_rect d' hd'))
                           (domino_cell2_row_le' (T.dominos_in_rect d' hd'))
      constructor
      · exact ⟨d', hd', rfl⟩
      · rw [reflectDomino3_cells]
        simp only [Finset.mem_image]
        exact ⟨c', hc'_in_d', hc'_eq⟩
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe] at hd1 hd2
    obtain ⟨d1', hd1', rfl⟩ := hd1
    obtain ⟨d2', hd2', rfl⟩ := hd2
    -- d1' ≠ d2' (since reflectDomino3 is injective)
    have hne' : d1' ≠ d2' := by
      intro heq
      apply hne
      subst heq
      rfl
    -- Use the disjointness of d1' and d2' in T
    have hdisj := T.pairwise_disjoint d1' hd1' d2' hd2' hne'
    -- reflectDomino3 preserves disjointness
    rw [reflectDomino3_cells, reflectDomino3_cells]
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Finset.mem_image] at hc1 hc2
    obtain ⟨c1', hc1', rfl⟩ := hc1
    obtain ⟨c2', hc2', rfl⟩ := hc2
    -- reflectCell3 c1' = reflectCell3 c2' implies c1' = c2'
    have hc1'_rect : c1' ∈ Rectangle n 3 := T.dominos_in_rect d1' hd1' hc1'
    have hc2'_rect : c2' ∈ Rectangle n 3 := T.dominos_in_rect d2' hd2' hc2'
    have heq' := reflectCell3_injective_on_rect hc1'_rect hc2'_rect heq
    exact hdisj c1' hc1' c2' hc2' heq'

end DominoTilings
