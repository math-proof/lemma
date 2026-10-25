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
import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def pairSourceBoxCurrentMeasure
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨(currentPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
      (fun _ => by positivity) {x, y}
      (boxCurrentSum_pair_pos d n beta hbeta x y hxy)).toMeasure.map
      (extendBoxCurrent d n),
    inferInstance⟩


end StatMech.FrontierB
