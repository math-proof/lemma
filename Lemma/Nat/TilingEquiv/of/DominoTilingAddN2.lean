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
  (T : DominoTiling (n + 2) 2) :
-- imply
  TilingEquiv (tiling_2_from_sum (tiling_2_to_sum T)) T := by
-- proof
  unfold TilingEquiv tiling_2_to_sum tiling_2_from_sum
  split_ifs with hv
  ·
    -- Vertical case: hasVerticalFirstColumn T
    simp only [Sum.elim_inr]
    -- We need: (prependVertical (restrictAfterVerticalGen T v ...)).dominos.image cells = T.dominos.image cells
    let v := Classical.choose hv
    let hv_spec := Classical.choose_spec hv
    let hv_mem := hv_spec.1
    let hv_cells := hv_spec.2
    -- The roundtrip dominos are:
    -- insert vertical_1_1 ((restrictAfterVerticalGen T v hv_mem hv_cells).dominos.image (shiftNat 1))
    -- = insert vertical_1_1 (((T.dominos.erase v).attach.image (shiftNeg 1)).image (shiftNat 1))
    simp only [prependVertical, restrictAfterVerticalGen]
    -- Now we need to show:
    -- (insert vertical_1_1 (((T.dominos.erase v).attach.image ...).image (shiftNat 1))).image cells
    -- = T.dominos.image cells
    rw [Finset.image_insert]
    -- LHS = insert (vertical_1_1.cells) (((...).image (shiftNat 1)).image cells)
    -- We need to show this equals T.dominos.image cells
    -- Step 1: Show (((...).image (shiftNat 1)).image cells = (T.dominos.erase v).image cells
    have hshift : ∀ d (hd : d ∈ T.dominos.erase v),
        ((d.shiftNeg 1 (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).1
          (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).2).shiftNat 1).cells = d.cells := by
      intro d hd
      exact Domino.shiftNat_shiftNeg_cells d 1 _ _
    have heq_erase := image_preserved_under_double_roundtrip' (T.dominos.erase v)
      (fun d hd => d.shiftNeg 1
        (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).1
        (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).2)
      (fun d => d.shiftNat 1) Domino.cells hshift
    rw [heq_erase]
    -- Now: insert (vertical_1_1.cells) ((T.dominos.erase v).image cells) = T.dominos.image cells
    -- Since vertical_1_1.cells = v.cells, this follows from insert_erase_image_eq'
    have hv_cells_eq :
      vertical_1_1.cells = v.cells := by rw [vertical_1_1_cells, hv_cells]
    rw [hv_cells_eq]
    exact insert_erase_image_eq' T.dominos v Domino.cells hv_mem
  ·
    -- Horizontal case: ¬hasVerticalFirstColumn T
    simp only [Sum.elim_inl]
    -- Get the horizontal pair dominos from the hypothesis
    let hpair := horizontalPair_of_not_hasVerticalFirstColumn T hv
    let d1 := Classical.choose hpair.1
    let hd1_spec := Classical.choose_spec hpair.1
    let hd1_mem := hd1_spec.1
    let hd1_cells := hd1_spec.2
    let d2 := Classical.choose hpair.2
    let hd2_spec := Classical.choose_spec hpair.2
    let hd2_mem := hd2_spec.1
    let hd2_cells := hd2_spec.2
    -- The roundtrip dominos are:
    -- insert horizontal_1_1 (insert horizontal_1_2 ((restrictAfterHorizontalPairGen T d1 d2 ...).dominos.image (shiftNat 2)))
    simp only [prependHorizontalPair, restrictAfterHorizontalPairGen]
    -- Now we need to show:
    -- (insert horizontal_1_1 (insert horizontal_1_2 (((T.dominos.erase d1).erase d2).attach.image ...).image (shiftNat 2))).image cells
    -- = T.dominos.image cells
    rw [Finset.image_insert, Finset.image_insert]
    -- LHS = insert (horizontal_1_1.cells) (insert (horizontal_1_2.cells) (((...).image (shiftNat 2)).image cells))
    -- Step 1: Show (((...).image (shiftNat 2)).image cells = ((T.dominos.erase d1).erase d2).image cells
    have hshift : ∀ d (hd : d ∈ (T.dominos.erase d1).erase d2),
        let hd' := Finset.mem_erase.mp hd
        let hd'' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)
        let hcols := other_dominos_col_ge_3_gen T d1 d2 hd1_mem hd2_mem hd1_cells hd2_cells d
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hd''.1 hd'.1
        ((d.shiftNeg 2 hcols.1 hcols.2).shiftNat 2).cells = d.cells := by
      intro d hd
      exact Domino.shiftNat_shiftNeg_cells d 2 _ _
    have heq_erase := image_preserved_under_double_roundtrip' ((T.dominos.erase d1).erase d2)
      (fun d hd =>
        let hd' := Finset.mem_erase.mp hd
        let hd'' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)
        let hcols := other_dominos_col_ge_3_gen T d1 d2 hd1_mem hd2_mem hd1_cells hd2_cells d
                      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hd''.1 hd'.1
        d.shiftNeg 2 hcols.1 hcols.2)
      (fun d => d.shiftNat 2) Domino.cells hshift
    rw [heq_erase]
    -- Now: insert (horizontal_1_1.cells) (insert (horizontal_1_2.cells) (((T.dominos.erase d1).erase d2).image cells))
    --    = T.dominos.image cells
    -- Since horizontal_1_1.cells = d1.cells and horizontal_1_2.cells = d2.cells,
    -- this follows from insert_insert_erase_erase_image_eq
    have hd1_cells_eq :
      horizontal_1_1.cells = d1.cells := by rw [horizontal_1_1_cells, hd1_cells]
    have hd2_cells_eq :
      horizontal_1_2.cells = d2.cells := by rw [horizontal_1_2_cells, hd2_cells]
    rw [hd1_cells_eq, hd2_cells_eq]
    exact insert_insert_erase_erase_image_eq T.dominos d1 d2 Domino.cells hd1_mem hd2_mem


-- created on 2026-10-20
