import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
open StatMech StatMech.Universality


/--
[hlhda_physical_white_depth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCutBounds.lean)
-/
@[path]
private lemma hlhda_physical_white_depth_pos_eq
  {ws : List ℤ}
  {T : ℕ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW)
  (hbounds : ∀ j, j ≤ ws.length → 0 ≤ hlhd_depth ws hleg j ∧ hlhd_depth ws hleg j ≤ T)
  (hk : k < ws.length)
  (hwhite : (hlhc_prefixCoord ws hleg.1 k).color = .white) :
-- imply
  0 < hlhd_depth ws hleg k := by
-- proof
  apply StatMech.Universality.hlhda_physical_white_depth_pos ws hleg T hbounds hk hwhite

/--
[hlhda_physical_black_depth_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCutBounds.lean)
-/
@[path]
private lemma hlhda_physical_black_depth_lt_eq
  {ws : List ℤ}
  {T : ℕ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW)
  (hT : 0 < T)
  (hbounds : ∀ j, j ≤ ws.length → 0 ≤ hlhd_depth ws hleg j ∧ hlhd_depth ws hleg j ≤ T)
  (hk : k < ws.length)
  (hblack : (hlhc_prefixCoord ws hleg.1 k).color = .black) :
-- imply
  hlhd_depth ws hleg k < T := by
-- proof
  apply StatMech.Universality.hlhda_physical_black_depth_lt ws hleg T hT hbounds hk hblack

/--
[hlhda_physical_book_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCutBounds.lean)
-/
@[path]
private lemma hlhda_physical_book_bounds_eq
  {ws : List ℤ}
  {T : ℕ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW)
  (hT : 0 < T)
  (hbounds : ∀ j, j ≤ ws.length → 0 ≤ hlhd_depth ws hleg j ∧ hlhd_depth ws hleg j ≤ T)
  (hk : k < ws.length) :
-- imply
  0 ≤ hexAWBookRe2 (hlhc_prefixCoord ws hleg.1 k) ∧ hexAWBookRe2 (hlhc_prefixCoord ws hleg.1 k) ≤ 3 * T := by
-- proof
  apply StatMech.Universality.hlhda_physical_book_bounds ws hleg T hT hbounds hk


-- created on 2026-10-23
