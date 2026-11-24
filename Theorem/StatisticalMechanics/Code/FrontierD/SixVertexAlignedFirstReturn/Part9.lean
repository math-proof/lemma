module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part11
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

@[simp] theorem doubledAlignedBranchSwap_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) :
    (doubledAlignedBranchSwap x).1 = x.1 := rfl

@[simp] theorem doubledAlignedBranchSwap_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) :
    doubledAlignedBranchSwap (doubledAlignedBranchSwap x) = x := by
  rcases x with ⟨d, branch⟩
  cases branch <;>
    simp [doubledAlignedBranchSwap]

end StatMech.FrontierD
