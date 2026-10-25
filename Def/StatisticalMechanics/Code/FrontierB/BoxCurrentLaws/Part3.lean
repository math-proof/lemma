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
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part2
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def freeBoxCurrentMeasure (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨((sourcelessCurrentPMF (StatMech.FK.boxGraph d n) beta
      (fun _ => 1) hbeta (fun _ => by positivity)).toMeasure).map
      (extendBoxCurrent d n),
    inferInstance⟩


noncomputable def boxCurrentInterior (d n : ℕ) :
    Finset (StatMech.FK.boxVerts d n) :=
  Finset.univ.filter (fun x => ¬ StatMech.FK.boxBoundary d n x)


noncomputable def plusBoxCurrentMeasure (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨((boundaryCurrentPMF (StatMech.FK.boxGraph d n) beta
      (fun _ => 1) hbeta (fun _ => by positivity)
      (boxCurrentInterior d n)).toMeasure).map
      (extendBoxCurrent d n),
    inferInstance⟩


end StatMech.FrontierB
