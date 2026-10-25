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
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part5
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


theorem interactionBoxEdgeIncl_injective (d n : Nat) :
    Function.Injective (interactionBoxEdgeIncl d n) := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective hef


end StatMech.FrontierB
