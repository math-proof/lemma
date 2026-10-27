import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusReduceSite_add_period_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma torusReduceSite_add_period_x_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : Site 2} :
-- imply
  torusReduceSite L (z + ![(L : ℤ), 0]) = torusReduceSite L z := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_add_period_x L z

/--
[torusReduceSite_add_period_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma torusReduceSite_add_period_y_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : Site 2} :
-- imply
  torusReduceSite L (z + ![0, (L : ℤ)]) = torusReduceSite L z := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_add_period_y L z

/--
[torusPlanarPullback_translate_period_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma torusPlanarPullback_translate_period_x_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  translateConfig ![(L : ℤ), 0] (torusPlanarPullback L omega) = torusPlanarPullback L omega := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPullback_translate_period_x L omega

/--
[torusPlanarPullback_translate_period_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma torusPlanarPullback_translate_period_y_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  translateConfig ![0, (L : ℤ)] (torusPlanarPullback L omega) = torusPlanarPullback L omega := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPullback_translate_period_y L omega

/--
[torusPlanarPullback_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma torusPlanarPullback_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (torusPlanarPullback L) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPullback_injective L

/--
[bdcTorusVerticalWinding_projects_to_closed_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma bdcTorusVerticalWinding_projects_to_closed_torus_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
-- given
  (h : bdcTorusVerticalWinding L omega) :
-- imply
  ∃ x y : Site 2, Connected 2 (torusPlanarPullback L omega) x y ∧ torusReduceSite L x = torusReduceSite L y ∧ x ≠ y := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusVerticalWinding_projects_to_closed_torus L omega h

/--
[torusSquareHorizontalCrossing_period_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma torusSquareHorizontalCrossing_period_false_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  ¬ torusSquareHorizontalCrossing L L omega := by
-- proof
  apply StatMech.BeffaraDC.torusSquareHorizontalCrossing_period_false L omega

/--
[bdcTorusVerticalWinding_not_representable_by_periodSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma bdcTorusVerticalWinding_not_representable_by_periodSquare_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
-- given
  (_h : bdcTorusVerticalWinding L omega) :
-- imply
  ¬ torusSquareHorizontalCrossing L L omega := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusVerticalWinding_not_representable_by_periodSquare L omega _h

/--
[mem_bdcTorusThinCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma mem_bdcTorusThinCrossingEvent_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  omega ∈ bdcTorusThinCrossingEvent L alpha n ↔ bdcTorusThinCrossing L alpha n omega := by
-- proof
  apply StatMech.BeffaraDC.mem_bdcTorusThinCrossingEvent L alpha n omega

/--
[bdcTorusThinCrossing_iff_pullback_mem_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma bdcTorusThinCrossing_iff_pullback_mem_union_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  bdcTorusThinCrossing L alpha n omega ↔ torusPlanarPullback L omega ∈ bdcLongRectangleUnion alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusThinCrossing_iff_pullback_mem_union L alpha n omega

/--
[bdcTorusThinCrossing_planarLift_subset_longRectangleUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma bdcTorusThinCrossing_planarLift_subset_longRectangleUnion_eq
  {L alpha n : ℕ}
  [Fact (2 < L)] :
-- imply
  bdcTorusPlanarLiftEvent L {omega | bdcTorusThinCrossing L alpha n omega} ⊆ bdcLongRectangleUnion alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusThinCrossing_planarLift_subset_longRectangleUnion L alpha n

/--
[BdcTorusWindingToThinCover.planarLift_subset_longRectangleUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma planarLift_subset_longRectangleUnion_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {W : Set (TorusAmbientConfig L)}
-- given
  (h : BdcTorusWindingToThinCover L alpha n W) :
-- imply
  bdcTorusPlanarLiftEvent L W ⊆ bdcLongRectangleUnion alpha n := by
-- proof
  apply StatMech.BeffaraDC.BdcTorusWindingToThinCover.planarLift_subset_longRectangleUnion h

/--
[bdcTorusVerticalWinding_planarLift_subset_longRectangleUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean)
-/
@[path]
private lemma bdcTorusVerticalWinding_planarLift_subset_longRectangleUnion_eq
  {alpha n : ℕ}
  [Fact (2 < bdcLongRectanglePeriod alpha n)]
-- given
  (h : BdcTorusVerticalWindingThinCover alpha n) :
-- imply
  bdcTorusPlanarLiftEvent (bdcLongRectanglePeriod alpha n) {omega | bdcTorusVerticalWinding (bdcLongRectanglePeriod alpha n) omega} ⊆ bdcLongRectangleUnion alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusVerticalWinding_planarLift_subset_longRectangleUnion h


-- created on 2026-10-23
