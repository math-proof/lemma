/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Structure.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part3
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem generalInteractionCurrentSubsequencePackage {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    GeneralInteractionCurrentSubsequencePackage I beta hbeta where
  subsequence_strict := generalCurrentBoxSubsequence_strictMono I beta hbeta
  free_weak := generalFreeBoxCurrentMeasure_tendsto_infinite I beta hbeta
  plus_weak := generalPlusBoxCurrentMeasure_tendsto_infinite I beta hbeta
  free_cylinder := generalFreeBoxCurrentMeasure_cylinder_tendsto_infinite I beta hbeta
  plus_cylinder := generalPlusBoxCurrentMeasure_cylinder_tendsto_infinite I beta hbeta

end StatMech.FrontierB
