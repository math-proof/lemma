/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part19
open StatMech.FrontierD


namespace ScratchLocalRetieC

noncomputable def alignedPermOrderedFixedPoints
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List D :=
  (Finset.univ.filter fun d => sigma d = d).toList

noncomputable def alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List D :=
  permOrderedAllCycles sigma ++ alignedPermOrderedFixedPoints sigma

noncomputable def alignedPermOrderedAllOrbitLists
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List (List D) :=
  alignedPermOrderedCycleFactorLists sigma ++
    (alignedPermOrderedFixedPoints sigma).map fun d => [d]

end ScratchLocalRetieC
