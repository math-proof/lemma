import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusWindingThinObstruction
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[windingThinCounterexampleConfig_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexampleConfig_horizontal_eq
  {x y : ZMod 8} :
-- imply
  windingThinCounterexampleConfig (torusHorizontalEdge 8 x y) = decide (y = 0 ∨ x = y) := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexampleConfig_horizontal x y

/--
[windingThinCounterexampleConfig_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexampleConfig_vertical_eq
  {x y : ZMod 8} :
-- imply
  windingThinCounterexampleConfig (torusVerticalEdge 8 x y) = decide (x = y + 1) := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexampleConfig_vertical x y

/--
[windingThinCounterexample_diagHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_diagHorizontal_eq
  {t : ℤ} :
-- imply
  IsOpenEdge 2 (torusPlanarPullback 8 windingThinCounterexampleConfig) ![t, t] ![t + 1, t] := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_diagHorizontal t

/--
[windingThinCounterexample_diagVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_diagVertical_eq
  {t : ℤ} :
-- imply
  IsOpenEdge 2 (torusPlanarPullback 8 windingThinCounterexampleConfig) ![t + 1, t] ![t + 1, t + 1] := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_diagVertical t

/--
[windingThinCounterexample_rowEight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_rowEight_eq
  {t : ℤ} :
-- imply
  IsOpenEdge 2 (torusPlanarPullback 8 windingThinCounterexampleConfig) ![t, 8] ![t + 1, 8] := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_rowEight t

/--
[windingThinCounterexample_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_winds_eq :
-- imply
  bdcTorusVerticalWinding 8 windingThinCounterexampleConfig := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_winds

/--
[windingThinCounterexample_vertical_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_vertical_iff_eq
  {x y : ℤ} :
-- imply
  torusPlanarPullback 8 windingThinCounterexampleConfig s(![x, y], ![x, y + 1]) = true ↔ (x : ZMod 8) = (y : ZMod 8) + 1 := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_vertical_iff x y

/--
[windingThinCounterexample_cut_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_cut_step_eq
  {a c h : ℤ}
  {p q : Site 2}
-- given
  (hp : p ∈ rect a (a + 2) c (c + 4))
  (hq : q ∈ rect a (a + 2) c (c + 4))
  (hadj : (hypercubicLattice 2).Adj p q)
  (hopen : torusPlanarPullback 8 windingThinCounterexampleConfig s(p, q) = true)
  (hple : p 1 ≤ h)
  (hmiss : ∀ x : ℤ, a ≤ x → x ≤ a + 2 → (x : ZMod 8) ≠ (h : ZMod 8) + 1) :
-- imply
  q 1 ≤ h := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_cut_step hp hq hadj hopen hple hmiss

/--
[windingThinCounterexample_cut_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_cut_walk_eq
  {a c h : ℤ}
  {p q : (rect a (a + 2) c (c + 4) : Set (Site 2))}
  {w : (openSubgraphInduce 2 (torusPlanarPullback 8 windingThinCounterexampleConfig) (rect a (a + 2) c (c + 4))).Walk p q}
-- given
  (hmiss : ∀ x : ℤ, a ≤ x → x ≤ a + 2 → (x : ZMod 8) ≠ (h : ZMod 8) + 1)
  (hp : (p : Site 2) 1 ≤ h) :
-- imply
  (q : Site 2) 1 ≤ h := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_cut_walk hmiss w hp

/--
[windingThinCounterexample_no_vertical_of_missing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_no_vertical_of_missing_eq
  {a c h : ℤ}
-- given
  (hch : c ≤ h)
  (hhc : h < c + 4)
  (hmiss : ∀ x : ℤ, a ≤ x → x ≤ a + 2 → (x : ZMod 8) ≠ (h : ZMod 8) + 1) :
-- imply
  ¬ VerticalCrossing (torusPlanarPullback 8 windingThinCounterexampleConfig) a (a + 2) c (c + 4) := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_no_vertical_of_missing hch hhc hmiss

/--
[windingThinCounterexample_exists_missing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_exists_missing_eq
  {a c : ℤ}
-- given
  (ha0 : 0 ≤ a)
  (ha7 : a ≤ 7)
  (hc : c = 0 ∨ c = 4) :
-- imply
  ∃ h : ℤ, c ≤ h ∧ h < c + 4 ∧ ∀ x : ℤ, a ≤ x → x ≤ a + 2 → (x : ZMod 8) ≠ (h : ZMod 8) + 1 := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_exists_missing a c ha0 ha7 hc

/--
[windingThinCounterexample_not_thin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_not_thin_eq :
-- imply
  ¬ bdcTorusThinCrossing 8 2 1 windingThinCounterexampleConfig := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_not_thin

/--
[windingThinCounterexample_winding_not_thin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma windingThinCounterexample_winding_not_thin_eq :
-- imply
  bdcTorusVerticalWinding 8 windingThinCounterexampleConfig ∧ ¬ bdcTorusThinCrossing 8 2 1 windingThinCounterexampleConfig := by
-- proof
  apply StatMech.BeffaraDC.windingThinCounterexample_winding_not_thin

/--
[not_bdcTorusVerticalWindingThinCover_two_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean)
-/
@[path]
private lemma not_bdcTorusVerticalWindingThinCover_two_one_eq :
-- imply
  ¬ BdcTorusVerticalWindingThinCover 2 1 := by
-- proof
  apply StatMech.BeffaraDC.not_bdcTorusVerticalWindingThinCover_two_one


-- created on 2026-10-23
