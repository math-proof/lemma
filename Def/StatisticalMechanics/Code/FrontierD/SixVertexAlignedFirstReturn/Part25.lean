module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part22
open StatMech.FrontierD


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

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

end StatMech.FrontierD
