import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_is_horizontal_or_is_vertical
-- given
  (d : DominoTilings.Domino) :
-- imply
  d.isHorizontal ∨ d.isVertical := by
-- proof
  apply DominoTilings.Domino.isHorizontal_or_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_not_is_horizontal_and_is_vertical
-- given
  (d : DominoTilings.Domino) :
-- imply
  ¬(d.isHorizontal ∧ d.isVertical) := by
-- proof
  apply DominoTilings.Domino.not_isHorizontal_and_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_is_horizontal_iff_not_is_vertical_iff
-- given
  (d : DominoTilings.Domino) :
-- imply
  d.isHorizontal ↔ ¬d.isVertical := by
-- proof
  apply DominoTilings.Domino.isHorizontal_iff_not_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_is_vertical_iff_not_is_horizontal_iff
-- given
  (d : DominoTilings.Domino) :
-- imply
  d.isVertical ↔ ¬d.isHorizontal := by
-- proof
  apply DominoTilings.Domino.isVertical_iff_not_isHorizontal d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_is_horizontal_xor_is_vertical
-- given
  (d : DominoTilings.Domino) :
-- imply
  Xor d.isHorizontal d.isVertical := by
-- proof
  apply DominoTilings.Domino.isHorizontal_xor_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_tiling_equiv_refl
-- given
  (T : DominoTilings.DominoTiling n m) :
-- imply
  DominoTilings.DominoTiling.TilingEquiv T T := by
-- proof
  apply DominoTilings.DominoTiling.tilingEquiv_refl T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_tiling_equiv_symm
  {T₁ T₂ : DominoTilings.DominoTiling n m}
-- given
  (h : DominoTilings.DominoTiling.TilingEquiv T₁ T₂) :
-- imply
  DominoTilings.DominoTiling.TilingEquiv T₂ T₁ := by
-- proof
  apply DominoTilings.DominoTiling.tilingEquiv_symm h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_tiling_equiv_trans
  {T₁ T₂ T₃ : DominoTilings.DominoTiling n m}
-- given
  (h₀ : DominoTilings.DominoTiling.TilingEquiv T₁ T₂)
  (h₁ : DominoTilings.DominoTiling.TilingEquiv T₂ T₃) :
-- imply
  DominoTilings.DominoTiling.TilingEquiv T₁ T₃ := by
-- proof
  apply DominoTilings.DominoTiling.tilingEquiv_trans h₀ h₁

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_image_erase_insert_eq_eq
  [DecidableEq α] [DecidableEq β]
-- given
  (S : Finset α) (v w : α) (f : α → β)
  (hv : v ∈ S)
  (hf : f v = f w) :
-- imply
  (insert w (S.erase v)).image f = S.image f := by
-- proof
  apply DominoTilings.DominoTiling.image_erase_insert_eq S v w f hv hf

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma reflect_tiling3_is_faultfree_is
  {n : ℕ}
-- given
  (T : DominoTilings.DominoTiling n 3)
  (hfree : T.isFaultfree) :
-- imply
  (DominoTilings.reflectTiling3 T).isFaultfree := by
-- proof
  apply DominoTilings.reflectTiling3_isFaultfree T hfree

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma reflect_tiling3_has_top_vertical_iff_has_bottom_vertical_iff
  {n : ℕ}
-- given
  (T : DominoTilings.DominoTiling n 3)
  (c : ℕ) :
-- imply
  (DominoTilings.reflectTiling3 T).hasTopVerticalInCol c ↔
    T.hasBottomVerticalInCol c := by
-- proof
  apply DominoTilings.reflectTiling3_hasTopVertical_iff_hasBottomVertical T c

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma reflect_tiling3_involutive_eq
  {n : ℕ}
-- given
  (T : DominoTilings.DominoTiling n 3) :
-- imply
  DominoTilings.reflectTiling3 (DominoTilings.reflectTiling3 T) = T := by
-- proof
  apply DominoTilings.reflectTiling3_involutive T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma reflect_tiling3_preserves_tiling_equiv
  {n : ℕ}
-- given
  (T₁ T₂ : DominoTilings.DominoTiling n 3)
  (h : DominoTilings.DominoTiling.TilingEquiv T₁ T₂) :
-- imply
  DominoTilings.DominoTiling.TilingEquiv (DominoTilings.reflectTiling3 T₁)
    (DominoTilings.reflectTiling3 T₂) := by
-- proof
  apply DominoTilings.reflectTiling3_preserves_TilingEquiv T₁ T₂ h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma tiling_b_eq_reflect_tiling3_tiling_a_eq
-- given
  (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
-- imply
  DominoTilings.TilingB n hn hn_ge =
    DominoTilings.reflectTiling3 (DominoTilings.TilingA n hn hn_ge) := by
-- proof
  apply DominoTilings.TilingB_eq_reflectTiling3_TilingA n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma tiling_a_is_faultfree_is
-- given
  (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
-- imply
  (DominoTilings.TilingA n hn hn_ge).isFaultfree := by
-- proof
  apply DominoTilings.TilingA_isFaultfree n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma tiling_b_is_faultfree_is
-- given
  (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
-- imply
  (DominoTilings.TilingB n hn hn_ge).isFaultfree := by
-- proof
  apply DominoTilings.TilingB_isFaultfree n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma tiling_c_is_faultfree_is :
-- imply
  DominoTilings.TilingC.isFaultfree := by
-- proof
  apply DominoTilings.TilingC_isFaultfree

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma tiling_a_has_top_vertical
-- given
  (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
-- imply
  (DominoTilings.TilingA n hn hn_ge).hasTopVerticalInCol 1 := by
-- proof
  apply DominoTilings.TilingA_hasTopVertical n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma tiling_b_has_bottom_vertical
-- given
  (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
-- imply
  (DominoTilings.TilingB n hn hn_ge).hasBottomVerticalInCol 1 := by
-- proof
  apply DominoTilings.TilingB_hasBottomVertical n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma tiling_c_no_vertical_in_col1 :
-- imply
  ¬DominoTilings.TilingC.hasVerticalInCol 1 := by
-- proof
  apply DominoTilings.TilingC_noVerticalInCol1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma rectangle_tileable_iff_even
-- given
  (n : ℕ) :
-- imply
  Nonempty (DominoTilings.DominoTiling n 3) → Even n ∨ n = 0 := by
-- proof
  apply DominoTilings.rectangle_tileable_iff_even n

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma claim1_basement_middle_top
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3)
  (i : ℕ)
  (hfree : T.isFaultfree) (htop : T.hasTopVerticalInCol 1)
  (hi_pos : i ≥ 1) (hi_lt : i < n / 2) :
-- imply
  (∃ d ∈ T.dominos, d.cells = {(2 * i - 1, 1), (2 * i, 1)}) ∧
    (∃ d ∈ T.dominos, d.cells = {(2 * i, 2), (2 * i + 1, 2)}) ∧
    (∃ d ∈ T.dominos, d.cells = {(2 * i, 3), (2 * i + 1, 3)}) := by
-- proof
  apply DominoTilings.claim1_basement_middle_top n T hfree htop i hi_pos hi_lt

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma claim2_n_even
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3)
  (hfree : T.isFaultfree) (htop : T.hasTopVerticalInCol 1) :
-- imply
  Even n := by
-- proof
  apply DominoTilings.claim2_n_even n T hfree htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma faultfree_no_vertical_unique
-- given
  (T : DominoTilings.DominoTiling 2 3)
  (hfree : T.isFaultfree) (hno_vert : ¬T.hasVerticalInCol 1) :
-- imply
  DominoTilings.DominoTiling.TilingEquiv T DominoTilings.TilingC := by
-- proof
  apply DominoTilings.faultfree_no_vertical_unique T hfree hno_vert

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma faultfree_top_vertical_classification
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3)
  (hfree : T.isFaultfree) (htop : T.hasTopVerticalInCol 1) :
-- imply
  Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2),
    DominoTilings.DominoTiling.TilingEquiv T (DominoTilings.TilingA n hn hn_ge) := by
-- proof
  apply DominoTilings.faultfree_top_vertical_classification n T hfree htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma faultfree_bottom_vertical_classification
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3)
  (hfree : T.isFaultfree) (hbot : T.hasBottomVerticalInCol 1) :
-- imply
  Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2),
    DominoTilings.DominoTiling.TilingEquiv T (DominoTilings.TilingB n hn hn_ge) := by
-- proof
  apply DominoTilings.faultfree_bottom_vertical_classification n T hfree hbot

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma faultfree_classification
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3) (hfree : T.isFaultfree)
  (hn : n ≥ 1) :
-- imply
  (∃ (hn : Even n) (hn_ge : n ≥ 2),
      DominoTilings.DominoTiling.TilingEquiv T (DominoTilings.TilingA n hn hn_ge)) ∨
    (∃ (hn : Even n) (hn_ge : n ≥ 2),
      DominoTilings.DominoTiling.TilingEquiv T (DominoTilings.TilingB n hn hn_ge)) ∨
    (n = 2 ∧ ¬T.hasVerticalInCol 1 ∧ ∃ h : n = 2,
      DominoTilings.DominoTiling.TilingEquiv (h ▸ T) DominoTilings.TilingC) := by
-- proof
  apply DominoTilings.faultfree_classification n T hfree hn

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma card_rectangle_eq
-- given
  (n m : ℕ) :
-- imply
  (DominoTilings.Rectangle n m).card = n * m := by
-- proof
  apply DominoTilings.card_Rectangle n m

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma mem_rectangle_iff
  {n m : ℕ} {c : DominoTilings.Cell} :
-- imply
  c ∈ DominoTilings.Rectangle n m ↔ c.1 ≥ 1 ∧ c.1 ≤ n ∧ c.2 ≥ 1 ∧ c.2 ≤ m := by
-- proof
  apply DominoTilings.mem_Rectangle

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_card_cells_eq
-- given
  (d : DominoTilings.Domino) :
-- imply
  d.cells.card = 2 := by
-- proof
  apply DominoTilings.Domino.card_cells d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_shift_nat_cell1_eq
-- given
  (d : DominoTilings.Domino) (k : ℕ) :
-- imply
  (d.shiftNat k).cell1 = (d.cell1.1 + k, d.cell1.2) := by
-- proof
  apply DominoTilings.Domino.shiftNat_cell1 d k

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_shift_nat_cell2_eq
-- given
  (d : DominoTilings.Domino) (k : ℕ) :
-- imply
  (d.shiftNat k).cell2 = (d.cell2.1 + k, d.cell2.2) := by
-- proof
  apply DominoTilings.Domino.shiftNat_cell2 d k

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_neg_cell1_eq
-- given
  (d : DominoTilings.Domino) (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1) (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  (d.shiftNeg k h0 h1).cell1 = (d.cell1.1 - k, d.cell1.2) := by
-- proof
  apply DominoTilings.Domino.shiftNeg_cell1 d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_neg_cell2_eq
-- given
  (d : DominoTilings.Domino) (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1) (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  (d.shiftNeg k h0 h1).cell2 = (d.cell2.1 - k, d.cell2.2) := by
-- proof
  apply DominoTilings.Domino.shiftNeg_cell2 d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_neg_shift_nat_eq
-- given
  (d : DominoTilings.Domino)
  (hc1 : d.cell1.1 ≥ 1) (hc2 : d.cell2.1 ≥ 1)
  (k : ℕ) :
-- imply
  (d.shiftNat k).shiftNeg k (by simp [DominoTilings.Domino.shiftNat]; omega)
    (by simp [DominoTilings.Domino.shiftNat]; omega) = d := by
-- proof
  apply DominoTilings.Domino.shiftNeg_shiftNat d k hc1 hc2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_nat_shift_neg_eq
-- given
  (d : DominoTilings.Domino) (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1) (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  (d.shiftNeg k h0 h1).shiftNat k = d := by
-- proof
  apply DominoTilings.Domino.shiftNat_shiftNeg d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_nat_shift_neg_cells_eq
-- given
  (d : DominoTilings.Domino) (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1) (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  ((d.shiftNeg k h0 h1).shiftNat k).cells = d.cells := by
-- proof
  apply DominoTilings.Domino.shiftNat_shiftNeg_cells d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_shift_nat_injective
-- given
  (k : ℕ) :
-- imply
  Function.Injective (fun d : DominoTilings.Domino => d.shiftNat k) := by
-- proof
  apply DominoTilings.Domino.shiftNat_injective k

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_shift_neg_injective
  {d1 d2 : DominoTilings.Domino} {k : ℕ}
-- given
  (h1_1 : d1.cell1.1 ≥ k + 1) (h1_2 : d1.cell2.1 ≥ k + 1)
  (h2_1 : d2.cell1.1 ≥ k + 1) (h2_2 : d2.cell2.1 ≥ k + 1)
  (heq : d1.shiftNeg k h1_1 h1_2 = d2.shiftNeg k h2_1 h2_2) :
-- imply
  d1 = d2 := by
-- proof
  apply DominoTilings.Domino.shiftNeg_injective h1_1 h1_2 h2_1 h2_2 heq

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_nat_min_col_ge
-- given
  (d : DominoTilings.Domino)
  (hc1 : d.cell1.1 ≥ 1) (hc2 : d.cell2.1 ≥ 1)
  (k : ℕ) :
-- imply
  (d.shiftNat k).minCol ≥ k + 1 := by
-- proof
  apply DominoTilings.Domino.shiftNat_minCol_ge d k hc1 hc2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_nat_is_vertical
-- given
  (d : DominoTilings.Domino) (h : d.isVertical) (k : ℕ) :
-- imply
  (d.shiftNat k).isVertical := by
-- proof
  apply DominoTilings.Domino.shiftNat_isVertical d k h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_shift_nat_is_horizontal
-- given
  (d : DominoTilings.Domino) (h : d.isHorizontal) (k : ℕ) :
-- imply
  (d.shiftNat k).isHorizontal := by
-- proof
  apply DominoTilings.Domino.shiftNat_isHorizontal d k h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_cells_eq :
-- imply
  DominoTilings.vertical_1_1.cells = {(1, 1), (1, 2)} := by
-- proof
  apply DominoTilings.vertical_1_1_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma horizontal_1_1_cells_eq :
-- imply
  DominoTilings.horizontal_1_1.cells = {(1, 1), (2, 1)} := by
-- proof
  apply DominoTilings.horizontal_1_1_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma horizontal_1_2_cells_eq :
-- imply
  DominoTilings.horizontal_1_2.cells = {(1, 2), (2, 2)} := by
-- proof
  apply DominoTilings.horizontal_1_2_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_ne_horizontal_1_1 :
-- imply
  DominoTilings.vertical_1_1 ≠ DominoTilings.horizontal_1_1 := by
-- proof
  apply DominoTilings.vertical_1_1_ne_horizontal_1_1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_ne_horizontal_1_2 :
-- imply
  DominoTilings.vertical_1_1 ≠ DominoTilings.horizontal_1_2 := by
-- proof
  apply DominoTilings.vertical_1_1_ne_horizontal_1_2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma horizontal_1_1_ne_horizontal_1_2 :
-- imply
  DominoTilings.horizontal_1_1 ≠ DominoTilings.horizontal_1_2 := by
-- proof
  apply DominoTilings.horizontal_1_1_ne_horizontal_1_2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_flip_cells_eq :
-- imply
  DominoTilings.vertical_1_1_flip.cells = {(1, 2), (1, 1)} := by
-- proof
  apply DominoTilings.vertical_1_1_flip_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_flip_cells_eq_vertical_1_1 :
-- imply
  DominoTilings.vertical_1_1_flip.cells = DominoTilings.vertical_1_1.cells := by
-- proof
  apply DominoTilings.vertical_1_1_flip_cells_eq

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_ne_vertical_1_1_flip :
-- imply
  DominoTilings.vertical_1_1 ≠ DominoTilings.vertical_1_1_flip := by
-- proof
  apply DominoTilings.vertical_1_1_ne_vertical_1_1_flip

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma eq_vertical_1_1_of_cells_eq
-- given
  (d : DominoTilings.Domino) (h : d.cells = DominoTilings.vertical_1_1.cells) :
-- imply
  d = DominoTilings.vertical_1_1 ∨ d = DominoTilings.vertical_1_1_flip := by
-- proof
  apply DominoTilings.eq_vertical_1_1_of_cells_eq d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_not_in_shift_nat1_image
-- given
  (S : Finset DominoTilings.Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  DominoTilings.vertical_1_1 ∉ S.image (fun d => d.shiftNat 1) := by
-- proof
  apply DominoTilings.vertical_1_1_not_in_shiftNat1_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma horizontal_1_1_not_in_shift_nat2_image
-- given
  (S : Finset DominoTilings.Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  DominoTilings.horizontal_1_1 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilings.horizontal_1_1_not_in_shiftNat2_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma horizontal_1_2_not_in_shift_nat2_image
-- given
  (S : Finset DominoTilings.Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  DominoTilings.horizontal_1_2 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilings.horizontal_1_2_not_in_shiftNat2_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_1_1_not_in_shift_nat2_image
-- given
  (S : Finset DominoTilings.Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  DominoTilings.vertical_1_1 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilings.vertical_1_1_not_in_shiftNat2_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_domino_cells_col_ge_one
-- given
  (T : DominoTilings.DominoTiling n m) (d : DominoTilings.Domino) (hd : d ∈ T.dominos) :
-- imply
  d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1 := by
-- proof
  apply DominoTilings.DominoTiling.domino_cells_col_ge_one T d hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_domino_cells_row_ge_one
-- given
  (T : DominoTilings.DominoTiling n m) (d : DominoTilings.Domino) (hd : d ∈ T.dominos) :
-- imply
  d.cell1.2 ≥ 1 ∧ d.cell2.2 ≥ 1 := by
-- proof
  apply DominoTilings.DominoTiling.domino_cells_row_ge_one T d hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_other_dominos_col_ge_3
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2) (d : DominoTilings.Domino)
  (hh1 : DominoTilings.horizontal_1_1 ∈ T.dominos)
  (hh2 : DominoTilings.horizontal_1_2 ∈ T.dominos)
  (hd : d ∈ T.dominos)
  (hne1 : d ≠ DominoTilings.horizontal_1_1) (hne2 : d ≠ DominoTilings.horizontal_1_2) :
-- imply
  d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
-- proof
  apply DominoTilings.DominoTiling.other_dominos_col_ge_3 T hh1 hh2 d hd hne1 hne2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_card_eq_twice_dominos
-- given
  (T : DominoTilings.DominoTiling n m) :
-- imply
  (DominoTilings.Rectangle n m).card = 2 * T.dominos.card := by
-- proof
  apply DominoTilings.DominoTiling.card_eq_twice_dominos T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_cell_covered
-- given
  (T : DominoTilings.DominoTiling n m) (c : DominoTilings.Cell)
  (hc : c ∈ DominoTilings.Rectangle n m) :
-- imply
  ∃ d ∈ T.dominos, c ∈ d.cells := by
-- proof
  apply DominoTilings.DominoTiling.cell_covered T c hc

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_cell_covered_unique
-- given
  (T : DominoTilings.DominoTiling n m) (c : DominoTilings.Cell)
  (d₁ d₂ : DominoTilings.Domino) (hd₁ : d₁ ∈ T.dominos) (hd₂ : d₂ ∈ T.dominos)
  (hc₁ : c ∈ d₁.cells) (hc₂ : c ∈ d₂.cells) :
-- imply
  d₁ = d₂ := by
-- proof
  apply DominoTilings.DominoTiling.cell_covered_unique T c d₁ d₂ hd₁ hd₂ hc₁ hc₂

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_domino_col_ge_two_of_disjoint_from_first_col
-- given
  (T : DominoTilings.DominoTiling (n + 1) 2)
  (v d : DominoTilings.Domino)
  (hv : v ∈ T.dominos)
  (hv_cells : v.cells = DominoTilings.vertical_1_1.cells)
  (hd : d ∈ T.dominos) (hne : d ≠ v) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  apply DominoTilings.DominoTiling.domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd hne

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_domino_col_ge_two_of_ne_vertical
-- given
  (T : DominoTilings.DominoTiling (n + 1) 2) (d : DominoTilings.Domino)
  (hv : DominoTilings.vertical_1_1 ∈ T.dominos)
  (hd : d ∈ T.dominos)
  (hne : d ≠ DominoTilings.vertical_1_1) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  apply DominoTilings.DominoTiling.domino_col_ge_two_of_ne_vertical T hv d hd hne

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_restrict_after_vertical_prepend_vertical_eq
-- given
  (T : DominoTilings.DominoTiling n 2) :
-- imply
  DominoTilings.DominoTiling.restrictAfterVertical
    (DominoTilings.DominoTiling.prependVertical T)
    (by simp [DominoTilings.DominoTiling.prependVertical, DominoTilings.vertical_1_1]) = T := by
-- proof
  apply DominoTilings.DominoTiling.restrictAfterVertical_prependVertical T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_prepend_vertical_restrict_after_vertical_eq
-- given
  (T : DominoTilings.DominoTiling (n + 1) 2)
  (hv : DominoTilings.vertical_1_1 ∈ T.dominos) :
-- imply
  DominoTilings.DominoTiling.prependVertical
    (DominoTilings.DominoTiling.restrictAfterVertical T hv) = T := by
-- proof
  apply DominoTilings.DominoTiling.prependVertical_restrictAfterVertical T hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_restrict_after_horizontal_pair_prepend_horizontal_pair_eq
-- given
  (T : DominoTilings.DominoTiling n 2) :
-- imply
  DominoTilings.DominoTiling.restrictAfterHorizontalPair
    (DominoTilings.DominoTiling.prependHorizontalPair T)
    (by simp [DominoTilings.DominoTiling.prependHorizontalPair, DominoTilings.horizontal_1_1])
    (by simp [DominoTilings.DominoTiling.prependHorizontalPair, DominoTilings.horizontal_1_2]) = T := by
-- proof
  apply DominoTilings.DominoTiling.restrictAfterHorizontalPair_prependHorizontalPair T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_prepend_horizontal_pair_restrict_after_horizontal_pair_eq
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2)
  (hh1 : DominoTilings.horizontal_1_1 ∈ T.dominos)
  (hh2 : DominoTilings.horizontal_1_2 ∈ T.dominos) :
-- imply
  DominoTilings.DominoTiling.prependHorizontalPair
    (DominoTilings.DominoTiling.restrictAfterHorizontalPair T hh1 hh2) = T := by
-- proof
  apply DominoTilings.DominoTiling.prependHorizontalPair_restrictAfterHorizontalPair T hh1 hh2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_exists_domino_covering_11
-- given
  (T : DominoTilings.DominoTiling (n + 1) 2) :
-- imply
  ∃ d ∈ T.dominos, (1, 1) ∈ d.cells := by
-- proof
  apply DominoTilings.DominoTiling.exists_domino_covering_11 T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_domino_covering_11_cells
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2) (d : DominoTilings.Domino)
  (hd : d ∈ T.dominos) (hcov : (1, 1) ∈ d.cells) :
-- imply
  d.cells = {(1, 1), (1, 2)} ∨ d.cells = {(1, 1), (2, 1)} := by
-- proof
  apply DominoTilings.DominoTiling.domino_covering_11_cells T d hd hcov

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_exists_domino_covering_12_of_horizontal
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2) (d : DominoTilings.Domino)
  (hd : d ∈ T.dominos) (hcells : d.cells = {(1, 1), (2, 1)}) :
-- imply
  ∃ d' ∈ T.dominos, d' ≠ d ∧ (1, 2) ∈ d'.cells := by
-- proof
  apply DominoTilings.DominoTiling.exists_domino_covering_12_of_horizontal T d hd hcells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_domino_covering_12_cells
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2) (d d' : DominoTilings.Domino)
  (hd : d ∈ T.dominos) (hd' : d' ∈ T.dominos) (hne : d' ≠ d)
  (hd_cells : d.cells = {(1, 1), (2, 1)}) (hd'_cov : (1, 2) ∈ d'.cells) :
-- imply
  d'.cells = {(1, 2), (2, 2)} := by
-- proof
  apply DominoTilings.DominoTiling.domino_covering_12_cells T d d' hd hd' hne hd_cells hd'_cov

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_restrict_after_vertical_gen_eq_restrict_after_vertical
-- given
  (T : DominoTilings.DominoTiling (n + 1) 2)
  (hv : DominoTilings.vertical_1_1 ∈ T.dominos) :
-- imply
  DominoTilings.DominoTiling.restrictAfterVerticalGen T DominoTilings.vertical_1_1 hv rfl =
    DominoTilings.DominoTiling.restrictAfterVertical T hv := by
-- proof
  apply DominoTilings.DominoTiling.restrictAfterVerticalGen_eq_restrictAfterVertical T hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_other_dominos_col_ge_3_gen
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2)
  (d1 d2 d : DominoTilings.Domino)
  (hd1 : d1 ∈ T.dominos) (hd2 : d2 ∈ T.dominos)
  (hd1_cells : d1.cells = ({(1, 1), (2, 1)} : Finset DominoTilings.Cell))
  (hd2_cells : d2.cells = ({(1, 2), (2, 2)} : Finset DominoTilings.Cell))
  (hd : d ∈ T.dominos) (hne1 : d ≠ d1) (hne2 : d ≠ d2) :
-- imply
  d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
-- proof
  apply DominoTilings.DominoTiling.other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d hd hne1 hne2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_has_vertical_first_column_or_horizontal_pair
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2) :
-- imply
  DominoTilings.DominoTiling.hasVerticalFirstColumn T ∨
    (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset DominoTilings.Cell)) ∧
      (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset DominoTilings.Cell)) := by
-- proof
  apply DominoTilings.DominoTiling.hasVerticalFirstColumn_or_horizontalPair T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_horizontal_pair_of_not_has_vertical_first_column
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2)
  (hnotvert : ¬DominoTilings.DominoTiling.hasVerticalFirstColumn T) :
-- imply
  (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset DominoTilings.Cell)) ∧
    (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset DominoTilings.Cell)) := by
-- proof
  apply DominoTilings.DominoTiling.horizontalPair_of_not_hasVerticalFirstColumn T hnotvert

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_vertical_1_1_or_flip_of_has_vertical_first_column
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2)
  (hvert : DominoTilings.DominoTiling.hasVerticalFirstColumn T) :
-- imply
  DominoTilings.vertical_1_1 ∈ T.dominos ∨ DominoTilings.vertical_1_1_flip ∈ T.dominos := by
-- proof
  apply DominoTilings.DominoTiling.vertical_1_1_or_flip_of_hasVerticalFirstColumn T hvert

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_vertical_1_1_flip_not_mem_of_vertical_1_1_mem
-- given
  (T : DominoTilings.DominoTiling n m)
  (hv : DominoTilings.vertical_1_1 ∈ T.dominos) :
-- imply
  DominoTilings.vertical_1_1_flip ∉ T.dominos := by
-- proof
  apply DominoTilings.DominoTiling.vertical_1_1_flip_not_mem_of_vertical_1_1_mem T hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_classical_choose_has_vertical_first_column_eq_vertical_1_1
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2)
  (hv_mem : DominoTilings.vertical_1_1 ∈ T.dominos)
  (hv : DominoTilings.DominoTiling.hasVerticalFirstColumn T) :
-- imply
  Classical.choose hv = DominoTilings.vertical_1_1 := by
-- proof
  apply DominoTilings.DominoTiling.classical_choose_hasVerticalFirstColumn_eq_vertical_1_1 T hv_mem hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_horizontal_1_1_unique_in_prepend_horizontal_pair
-- given
  (T : DominoTilings.DominoTiling n 2) (d : DominoTilings.Domino)
  (hd : d ∈ (DominoTilings.DominoTiling.prependHorizontalPair T).dominos)
  (hd_cells : d.cells = ({(1, 1), (2, 1)} : Finset DominoTilings.Cell)) :
-- imply
  d = DominoTilings.horizontal_1_1 := by
-- proof
  apply DominoTilings.DominoTiling.horizontal_1_1_unique_in_prependHorizontalPair T d hd hd_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_horizontal_1_2_unique_in_prepend_horizontal_pair
-- given
  (T : DominoTilings.DominoTiling n 2) (d : DominoTilings.Domino)
  (hd : d ∈ (DominoTilings.DominoTiling.prependHorizontalPair T).dominos)
  (hd_cells : d.cells = ({(1, 2), (2, 2)} : Finset DominoTilings.Cell)) :
-- imply
  d = DominoTilings.horizontal_1_2 := by
-- proof
  apply DominoTilings.DominoTiling.horizontal_1_2_unique_in_prependHorizontalPair T d hd hd_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_vertical_1_1_unique_in_prepend_vertical
-- given
  (T : DominoTilings.DominoTiling n 2) (d : DominoTilings.Domino)
  (hd : d ∈ (DominoTilings.DominoTiling.prependVertical T).dominos)
  (hd_cells : d.cells = ({(1, 1), (1, 2)} : Finset DominoTilings.Cell)) :
-- imply
  d = DominoTilings.vertical_1_1 := by
-- proof
  apply DominoTilings.DominoTiling.vertical_1_1_unique_in_prependVertical T d hd hd_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_tiling_2_to_sum_from_sum_eq
-- given
  (x : (DominoTilings.DominoTiling n 2) ⊕ (DominoTilings.DominoTiling (n + 1) 2)) :
-- imply
  DominoTilings.DominoTiling.tiling_2_to_sum
    (DominoTilings.DominoTiling.tiling_2_from_sum x) = x := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_to_sum_from_sum x

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_tiling_2_to_sum_surjective :
-- imply
  Function.Surjective (@DominoTilings.DominoTiling.tiling_2_to_sum n) := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_to_sum_surjective

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_tiling_2_from_sum_injective :
-- imply
  Function.Injective (@DominoTilings.DominoTiling.tiling_2_from_sum n) := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_from_sum_injective

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma domino_tiling_tiling_2_roundtrip_tiling_equiv
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2) :
-- imply
  DominoTilings.DominoTiling.TilingEquiv
    (DominoTilings.DominoTiling.tiling_2_from_sum
      (DominoTilings.DominoTiling.tiling_2_to_sum T)) T := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_roundtrip_TilingEquiv T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma domino_tiling_tiling_2_from_sum_surjective_up_to_tiling_equiv
-- given
  (T : DominoTilings.DominoTiling (n + 2) 2) :
-- imply
  ∃ x, DominoTilings.DominoTiling.TilingEquiv
    (DominoTilings.DominoTiling.tiling_2_from_sum x) T := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_from_sum_surjective_up_to_TilingEquiv T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma mk_horizontal_domino_cell1_eq
-- given
  (x y : ℕ) :
-- imply
  (DominoTilings.mkHorizontalDomino x y).cell1 = (x, y) := by
-- proof
  apply DominoTilings.mkHorizontalDomino_cell1 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma mk_horizontal_domino_cell2_eq
-- given
  (x y : ℕ) :
-- imply
  (DominoTilings.mkHorizontalDomino x y).cell2 = (x + 1, y) := by
-- proof
  apply DominoTilings.mkHorizontalDomino_cell2 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma mk_vertical_domino_cell1_eq
-- given
  (x y : ℕ) :
-- imply
  (DominoTilings.mkVerticalDomino x y).cell1 = (x, y) := by
-- proof
  apply DominoTilings.mkVerticalDomino_cell1 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma mk_vertical_domino_cell2_eq
-- given
  (x y : ℕ) :
-- imply
  (DominoTilings.mkVerticalDomino x y).cell2 = (x, y + 1) := by
-- proof
  apply DominoTilings.mkVerticalDomino_cell2 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma is_horizontal_mk_horizontal_domino
-- given
  (x y : ℕ) :
-- imply
  (DominoTilings.mkHorizontalDomino x y).isHorizontal := by
-- proof
  apply DominoTilings.isHorizontal_mkHorizontalDomino x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma is_vertical_mk_vertical_domino
-- given
  (x y : ℕ) :
-- imply
  (DominoTilings.mkVerticalDomino x y).isVertical := by
-- proof
  apply DominoTilings.isVertical_mkVerticalDomino x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]

private lemma reflect_cell3_involutive_eq
-- given
  (c : DominoTilings.Cell) (h0 : c.2 ≥ 1) (h1 : c.2 ≤ 3) :
-- imply
  DominoTilings.reflectCell3 (DominoTilings.reflectCell3 c) = c := by
-- proof
  apply DominoTilings.reflectCell3_involutive c h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma reflect_tiling3_dominos_min_col_max_col
  {n : ℕ}
-- given
  (T : DominoTilings.DominoTiling n 3) :
-- imply
  ∀ d ∈ T.dominos, ∃ d' ∈ (DominoTilings.reflectTiling3 T).dominos,
    d'.minCol = d.minCol ∧ d'.maxCol = d.maxCol := by
-- proof
  apply DominoTilings.reflectTiling3_dominos_minCol_maxCol T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma has_top_vertical_in_col_implies_n_ge
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3) (c : ℕ)
  (htop : T.hasTopVerticalInCol c) :
-- imply
  n ≥ c := by
-- proof
  apply DominoTilings.hasTopVerticalInCol_implies_n_ge n T c htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma base_case_basement
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3)
  (htop : T.hasTopVerticalInCol 1) (hn : n ≥ 2) :
-- imply
  ∃ d ∈ T.dominos, d.cells = {(1, 1), (2, 1)} := by
-- proof
  apply DominoTilings.base_case_basement n T htop hn

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma faultfree_has_top_vertical_in_col_implies_n_ge_two
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3)
  (hfree : T.isFaultfree) (htop : T.hasTopVerticalInCol 1) :
-- imply
  n ≥ 2 := by
-- proof
  apply DominoTilings.faultfree_hasTopVerticalInCol_implies_n_ge_two n T hfree htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma vertical_in_col1_trichotomy
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3) :
-- imply
  T.hasVerticalInCol 1 → T.hasTopVerticalInCol 1 ∨ T.hasBottomVerticalInCol 1 := by
-- proof
  apply DominoTilings.vertical_in_col1_trichotomy n T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma no_vertical_implies_n_eq_2
-- given
  (n : ℕ) (T : DominoTilings.DominoTiling n 3)
  (hfree : T.isFaultfree) (hno_vert : ¬T.hasVerticalInCol 1) (hn : n ≥ 1) :
-- imply
  n = 2 := by
-- proof
  apply DominoTilings.no_vertical_implies_n_eq_2 n T hfree hno_vert hn


-- created on 2026-10-11
-- updated on 2026-10-20
