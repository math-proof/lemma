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
import Def.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem pairSourceBoxCurrentMeasure_prod_apply
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d)))) (hC : MeasurableSet C) :
    ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _) C =
      (sourceCurrentPairPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1)
        hbeta.le (fun _ => by positivity) {x, y} {x, y}
        (boxCurrentSum_pair_pos d n beta hbeta x y hxy)
        (boxCurrentSum_pair_pos d n beta hbeta x y hxy)).toMeasure
          ((Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' C) := by
  let G := StatMech.FK.boxGraph d n
  let mu := (currentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) {x, y}
    (boxCurrentSum_pair_pos d n beta hbeta x y hxy)).toMeasure
  change (Measure.map (extendBoxCurrent d n) mu).prod
      (Measure.map (extendBoxCurrent d n) mu) C = _
  rw [Measure.map_prod_map mu mu (measurable_extendBoxCurrent d n)
    (measurable_extendBoxCurrent d n),
    Measure.map_apply
      ((measurable_extendBoxCurrent d n).prodMap
        (measurable_extendBoxCurrent d n)) hC,
    sourceCurrentPairPMF_toMeasure_eq_prod]


end StatMech.FrontierB
