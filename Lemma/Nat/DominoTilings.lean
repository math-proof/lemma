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


-- created on 2026-10-11
