/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part6


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


def kwExpandedRectilinearBlocks (blocks : List (Fin 4 × ℕ)) : List ℂ :=
  blocks.flatMap fun block ↦
    List.replicate block.2 (kwRectilinearVector block.1)


def kwCompressedRectilinearBlocks (blocks : List (Fin 4 × ℕ)) : List ℂ :=
  blocks.map fun block ↦ kwRectilinearVector block.1

end StatMech.FrontierA
