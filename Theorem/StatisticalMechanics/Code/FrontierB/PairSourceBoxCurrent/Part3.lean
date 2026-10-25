/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.SourceCurrentTail.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw.Part2
import Def.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part2
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem boxPairCorrelationConstant_pos
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) :
    0 < boxPairCorrelationConstant d n beta x y := by
  apply pathCorrelationConstant_pos (StatMech.FK.boxGraph d n) beta
    (fun _ => 1) Finset.univ (boxGraphPath d n x y) hbeta
  · intro e he
    positivity
  · intro z hz
    simp

theorem boxPairCorrelationConstant_le_expectation
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    boxPairCorrelationConstant d n beta x y ≤
      expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} := by
  exact pathCorrelationConstant_le_expectation
    (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) Finset.univ (boxGraphPath d n x y)
    (boxGraphPath_isPath d n x y) hxy


theorem pairSourceBoxCurrentMeasure_edge_tail
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (e : (StatMech.FK.boxGraph d n).edgeFinset) (K : ℕ) :
    (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} =
      (sourceCurrentMeasure (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta.le (fun _ => by positivity) {x, y}
        (boxCurrentSum_pair_pos d n beta hbeta x y hxy) :
          Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d n) _
      {m | K ≤ m (boxCurrentEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d n e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]


theorem pairSourceBoxCurrentMeasure_edge_inverse_tail_le
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (K : ℕ) (hK : 0 < K) :
    (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} ≤
      ENNReal.ofReal
        (Real.exp beta / (boxPairCorrelationConstant d n beta x y * K)) := by
  rw [pairSourceBoxCurrentMeasure_edge_tail]
  simpa using sourceCurrentMeasure_edge_inverse_tail_le
    (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) {x, y}
    (boxCurrentSum_pair_pos d n beta hbeta x y hxy) e
    (boxPairCorrelationConstant d n beta x y)
    (boxPairCorrelationConstant_pos d n beta hbeta x y)
    (boxPairCorrelationConstant_le_expectation d n beta hbeta x y hxy)
    K hK

end StatMech.FrontierB
