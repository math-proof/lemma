import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (T : DominoTiling n 3) :
-- imply
  reflectTiling3 (reflectTiling3 T) = T := by
-- proof
  -- Two DominoTilings are equal iff their dominos are equal (proof irrelevance for the rest)
  have h_dominos : (reflectTiling3 (reflectTiling3 T)).dominos = T.dominos := by
    ext d
    constructor
    ·
      -- d ∈ (reflectTiling3 (reflectTiling3 T)).dominos → d ∈ T.dominos
      intro hd
      rw [reflectTiling3] at hd
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨d', hd', heq⟩ := hd
      rw [reflectTiling3] at hd'
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe] at hd'
      obtain ⟨d'', hd'', heq'⟩ := hd'
      subst heq heq'
      have hd''_rect := T.dominos_in_rect d'' hd''
      have hge1 := domino_cell1_row_ge' hd''_rect
      have hge2 := domino_cell2_row_ge' hd''_rect
      have hle1 := domino_cell1_row_le' hd''_rect
      have hle2 := domino_cell2_row_le' hd''_rect
      have h1' : (reflectDomino3 d'' hle1 hle2).cell1.2 ≤ 3 := by
        simp only [reflectDomino3, reflectCell3]; omega
      have h2' : (reflectDomino3 d'' hle1 hle2).cell2.2 ≤ 3 := by
        simp only [reflectDomino3, reflectCell3]; omega
      have hinv : reflectDomino3 (reflectDomino3 d'' hle1 hle2) h1' h2' = d'' := by
        ext <;> simp only [reflectDomino3, reflectCell3] <;> omega
      rwa [hinv]
    ·
      -- d ∈ T.dominos → d ∈ (reflectTiling3 (reflectTiling3 T)).dominos
      intro hd
      have hd_rect := T.dominos_in_rect d hd
      have hge1 := domino_cell1_row_ge' hd_rect
      have hge2 := domino_cell2_row_ge' hd_rect
      have hle1 := domino_cell1_row_le' hd_rect
      have hle2 := domino_cell2_row_le' hd_rect
      rw [reflectTiling3]
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe]
      refine ⟨reflectDomino3 d hle1 hle2, ?_, ?_⟩
      ·
        rw [reflectTiling3]
        simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
          ← Function.Embedding.toFun_eq_coe]
        exact ⟨d, hd, rfl⟩
      · ext <;> simp only [reflectDomino3, reflectCell3] <;> omega
  -- Now use h_dominos to conclude equality
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    have h : (reflectTiling3 (reflectTiling3 { dominos, dominos_in_rect, covers_all, pairwise_disjoint })).dominos = dominos := h_dominos
    cases hT : reflectTiling3 (reflectTiling3 { dominos, dominos_in_rect, covers_all, pairwise_disjoint }) with
    | mk dominos' dominos_in_rect' covers_all' pairwise_disjoint' =>
      rw [hT] at h
      simp only at h
      subst h
      rfl


-- created on 2026-10-20
