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
import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceBoxCurrent
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice

open StatMech.IsingFK


noncomputable def plusPairSourceBoxCurrentMeasure
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨((boundarySourceCurrentPMF (StatMech.FK.boxGraph d (n + 1)) beta
      (fun _ => 1) hbeta.le (fun _ => by positivity)
      (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y}
      (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy)).toMeasure).map
      (extendBoxCurrent d (n + 1)),
    inferInstance⟩


end StatMech.FrontierB
