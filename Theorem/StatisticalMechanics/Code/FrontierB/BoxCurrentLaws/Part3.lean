/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem freeBoxCurrentMeasure_edge_tail (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) (e : (StatMech.FK.boxGraph d n).edgeFinset) (K : ℕ) :
    (freeBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} =
      (sourcelessCurrentMeasure (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity) :
          Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d n)
      ((sourcelessCurrentPMF (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity)).toMeasure)
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d n e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]


theorem plusBoxCurrentMeasure_edge_tail (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) (e : (StatMech.FK.boxGraph d n).edgeFinset) (K : ℕ) :
    (plusBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} =
      (boundaryCurrentMeasure (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n) :
          Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d n)
      ((boundaryCurrentPMF (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n)).toMeasure)
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d n e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]

end StatMech.FrontierB
