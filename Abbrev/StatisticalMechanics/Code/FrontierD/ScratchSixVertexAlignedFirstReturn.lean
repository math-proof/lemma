module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part10
open StatMech.FrontierD


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ScratchLocalRetieC

abbrev DoubledAlignedState
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  SixVertexOrientedDisagreementDart omega eta × Bool

end ScratchLocalRetieC
