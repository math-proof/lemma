module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn
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

def localPreferredPairing (p : SixVertexLocalIncomingPattern) : Bool :=
  if compatible false p then false else true

end StatMech.FrontierD
