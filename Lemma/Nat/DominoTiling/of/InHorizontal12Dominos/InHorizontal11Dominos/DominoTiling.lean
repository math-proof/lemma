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
-- given
  (T : DominoTiling (n + 2) 2)
  (hh1 : horizontal_1_1 ∈ T.dominos)
  (hh2 : horizontal_1_2 ∈ T.dominos) :
-- imply
  prependHorizontalPair (restrictAfterHorizontalPair T hh1 hh2) = T := by
-- proof
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependHorizontalPair restrictAfterHorizontalPair
    congr 1
    ext d
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    ·
      intro hd
      obtain rfl | rfl | ⟨d', hd'_mem, hd'_eq⟩ := hd
      · exact hh1
      · exact hh2
      ·
        obtain ⟨d'', hd''_erase, hd''_eq⟩ := hd'_mem
        have hd''_in := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd''_erase)
        have hd''_ne1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hd''_erase)).1
        have hd''_ne2 := (Finset.mem_erase.mp hd''_erase).1
        have hcols := other_dominos_col_ge_3
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ hh1 hh2 d'' hd''_in hd''_ne1 hd''_ne2
        rw [← hd'_eq, ← hd''_eq]
        rwa [Domino.shiftNat_shiftNeg]
    ·
      intro hd
      by_cases hne1 : d = horizontal_1_1
      ·
        left
        exact hne1
      ·
        by_cases hne2 : d = horizontal_1_2
        ·
          right
          left
          exact hne2
        ·
          right
          right
          have hd_erase : d ∈ (dominos.erase horizontal_1_1).erase horizontal_1_2 := 
            Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hd⟩⟩
          have hcols := other_dominos_col_ge_3
            ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ hh1 hh2 d hd hne1 hne2
          use d.shiftNeg 2 (by omega) (by omega)
          constructor
          · use d, hd_erase
          · exact Domino.shiftNat_shiftNeg d 2 (by omega) (by omega)


-- created on 2026-10-20
