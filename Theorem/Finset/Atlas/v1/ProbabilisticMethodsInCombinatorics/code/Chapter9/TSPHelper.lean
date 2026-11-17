module

public import Mathlib
public import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.TSPHelper

public section

open MeasureTheory Metric Set Real Filter TSPHelper


/--
[volume_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSPHelper.lean)
-/
public theorem volume_unitSquare_eq :
-- imply
  (volume : Measure (EuclideanSpace ℝ (Fin 2))) unitSquare = 1 := by
-- proof
  apply TSPHelper.volume_unitSquare


-- created on 2026-10-23
