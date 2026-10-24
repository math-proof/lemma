import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamImprovementBridge
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[grahamCov2_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamCov2_comm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (beta h : ℝ) :
-- imply
  cov2 G beta h x y = cov2 G beta h y x := by
-- proof
  apply StatMech.FrontierA.grahamCov2_comm G beta h x y

/--
[grahamCov2_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamCov2_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (beta h : ℝ) :
-- imply
  cov2 G beta h x x = 1 - onePt G beta h x ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamCov2_self G beta h x

/--
[grahamCov2_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamCov2_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ cov2 G beta h x y := by
-- proof
  apply StatMech.FrontierA.grahamCov2_nonneg G beta h hbeta hh x y

/--
[grahamImprovedGHSRHS_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamImprovedGHSRHS_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  grahamImprovedGHSRHS G beta h i j k ≤ 0 := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHSRHS_nonpos G beta h hbeta hh i j k

/--
[grahamGhostCorrectedRHS_le_leading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamGhostCorrectedRHS_le_leading_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  grahamGhostCorrectedRHS G beta h i j k ≤ grahamGhostLeadingRHS G beta h i j k := by
-- proof
  apply StatMech.FrontierA.grahamGhostCorrectedRHS_le_leading G beta h hbeta hh i j k

/--
[grahamGhostFourPoint_iff_improvedGHS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamGhostFourPoint_iff_improvedGHS_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : ℝ) :
-- imply
  gc_lebowitzU4 G beta h i j k ≤ grahamGhostCorrectedRHS G beta h i j k ↔ eg_ursell3 G beta h i j k ≤ grahamImprovedGHSRHS G beta h i j k := by
-- proof
  apply StatMech.FrontierA.grahamGhostFourPoint_iff_improvedGHS G beta h i j k

/--
[grahamGhostLeadingBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamGhostLeadingBound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  gc_lebowitzU4 G beta h i j k ≤ grahamGhostLeadingRHS G beta h i j k := by
-- proof
  apply StatMech.FrontierA.grahamGhostLeadingBound G beta h hbeta hh i j k

/--
[grahamImprovedGHS_zero_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamImprovedGHS_zero_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {i j k : V}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  eg_ursell3 G beta 0 i j k ≤ grahamImprovedGHSRHS G beta 0 i j k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_zero_field G beta hbeta i j k

/--
[grahamGhostCorrectedBound_zero_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamGhostCorrectedBound_zero_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {i j k : V}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  gc_lebowitzU4 G beta 0 i j k ≤ grahamGhostCorrectedRHS G beta 0 i j k := by
-- proof
  apply StatMech.FrontierA.grahamGhostCorrectedBound_zero_field G beta hbeta i j k

/--
[grahamUrsell3_last_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamUrsell3_last_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i k : V}
-- given
  (beta h : ℝ) :
-- imply
  eg_ursell3 G beta h i k k = -2 * onePt G beta h k * cov2 G beta h i k := by
-- proof
  apply StatMech.FrontierA.grahamUrsell3_last_repeated G beta h i k

/--
[grahamImprovedGHS_right_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamImprovedGHS_right_pivot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i k : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  eg_ursell3 G beta h i k k ≤ grahamImprovedGHSRHS G beta h i k k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_right_pivot G beta h hbeta hh i k

/--
[grahamImprovedGHS_left_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamImprovedGHS_left_pivot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j k : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  eg_ursell3 G beta h k j k ≤ grahamImprovedGHSRHS G beta h k j k := by
-- proof
  apply StatMech.FrontierA.grahamImprovedGHS_left_pivot G beta h hbeta hh j k

/--
[grahamGhostCorrectedBound_of_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamImprovementBridge.lean)
-/
@[path]
private lemma grahamGhostCorrectedBound_of_pivot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hpivot : i = k ∨ j = k) :
-- imply
  gc_lebowitzU4 G beta h i j k ≤ grahamGhostCorrectedRHS G beta h i j k := by
-- proof
  apply StatMech.FrontierA.grahamGhostCorrectedBound_of_pivot G beta h hbeta hh i j k hpivot


-- created on 2026-10-23
