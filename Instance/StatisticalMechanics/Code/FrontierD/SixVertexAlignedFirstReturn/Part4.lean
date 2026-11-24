module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part28
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

namespace FourByTwoPrefixBondAudit

instance (arrows : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable arrows.IceRule :=
  inferInstanceAs (Decidable (forall v, arrows.incomingCount v = 2))

instance (first second : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable (SixVertexLocallyDegreeTwo first second) := by
  unfold SixVertexLocallyDegreeTwo
  infer_instance

end FourByTwoPrefixBondAudit
end StatMech.FrontierD
