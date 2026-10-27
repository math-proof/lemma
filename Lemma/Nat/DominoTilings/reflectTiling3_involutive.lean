import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  {n : ℕ}
  (T : DominoTiling n 3) :
-- imply
  reflectTiling3 (reflectTiling3 T) = T := by
-- proof
  have h_dominos : (reflectTiling3 (reflectTiling3 T)).dominos = T.dominos := by
    ext d
    constructor
    ·
      intro hd
      simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨d', ⟨d'', hd'', rfl⟩, rfl⟩ := hd
      have hd''_rect := T.dominos_in_rect d'' hd''
      have hc1 := hd''_rect (mem_insert_self _ _)
      have hc2 := hd''_rect (mem_insert_of_mem (mem_singleton_self _))
      rw [mem_Rectangle] at hc1 hc2
      convert hd''
      apply Domino.ext
      ·
        change reflectCell3 (reflectCell3 d''.cell1) = d''.cell1
        simp only [reflectCell3]
        exact Prod.ext rfl (Nat.sub_sub_self (by omega : d''.cell1.2 ≤ 4))
      ·
        change reflectCell3 (reflectCell3 d''.cell2) = d''.cell2
        simp only [reflectCell3]
        exact Prod.ext rfl (Nat.sub_sub_self (by omega : d''.cell2.2 ≤ 4))
    ·
      intro hd
      have hd_rect := T.dominos_in_rect d hd
      have hc1 := hd_rect (mem_insert_self _ _)
      have hc2 := hd_rect (mem_insert_of_mem (mem_singleton_self _))
      rw [mem_Rectangle] at hc1 hc2
      simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe]
      refine ⟨_, ⟨d, hd, rfl⟩, ?_⟩
      ·
        apply Domino.ext
        ·
          change reflectCell3 (reflectCell3 d.cell1) = d.cell1
          simp only [reflectCell3]
          exact Prod.ext rfl (Nat.sub_sub_self (by omega : d.cell1.2 ≤ 4))
        ·
          change reflectCell3 (reflectCell3 d.cell2) = d.cell2
          simp only [reflectCell3]
          exact Prod.ext rfl (Nat.sub_sub_self (by omega : d.cell2.2 ≤ 4))
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    cases hT : reflectTiling3 (reflectTiling3 ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩) with
    | mk dominos' dominos_in_rect' covers_all' pairwise_disjoint' =>
      have h := h_dominos
      simp only [hT] at h
      subst h
      rfl


-- created on 2026-10-20
