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
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem boxCurrentSum_pair_pos
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    0 < currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} :=
  currentSum_pair_pos_of_path (StatMech.FK.boxGraph d n) beta
    (fun _ => 1) hbeta (fun _ => by positivity)
    (boxGraphPath d n x y) (boxGraphPath_isPath d n x y) hxy


end StatMech.FrontierB
