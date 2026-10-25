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
import Theorem.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part16
open StatMech.FrontierD


namespace ScratchLocalRetieC

noncomputable def alignedActiveBlackDartLayerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d} :=
  (doubledAlignedBlackDartEquiv homega heta hdegree false).symm.trans
    (doubledAlignedBlackDartEquiv homega heta hdegree true)

noncomputable def alignedBlackDartLayerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm (FKMedialBlackDart T) :=
  (alignedActiveBlackDartLayerSwap homega heta hdegree).extendDomain
    (Equiv.refl {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d})

end ScratchLocalRetieC
