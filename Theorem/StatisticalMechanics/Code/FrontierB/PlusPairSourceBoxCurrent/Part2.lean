/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierB.PlusPairSourceBoxCurrent.Part2
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice

open StatMech.IsingFK


theorem plusPairSourceBoxCurrentMeasure_edge_tail
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (e : (StatMech.FK.boxGraph d (n + 1)).edgeFinset) (K : ℕ) :
    (plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d (n + 1) e)} =
      (boundarySourceCurrentPMF (StatMech.FK.boxGraph d (n + 1)) beta
        (fun _ => 1) hbeta.le (fun _ => by positivity)
        (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y}
        (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy)).toMeasure
          {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d (n + 1)) _
      {m | K ≤ m (boxCurrentEdgeIncl d (n + 1) e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d (n + 1) e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d (n + 1) e))
      MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]

end StatMech.FrontierB
