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
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part17
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem alignedFirstReturnTime_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    finiteFirstReturnTime
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree false x) =
      finiteFirstReturnTime
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree true x) := by
  classical
  apply finiteFirstReturnTime_eq_of_aligned_first
    (alignedBoundaryPerm homega heta hdegree false)
    (alignedBoundaryPerm homega heta hdegree true)
    (activeBlackDart (omega := omega) (eta := eta))
    (activeBlackDart (omega := omega) (eta := eta)) (fun a b => a = b)
  · intro a b hab
    subst b
    rfl
  · intro a b hab hnotA hnotB
    subst b
    apply blackBoundary_eq_of_pairing_eq_at
    apply alignedRoutingPairing_eq_layers_at_inactive
      homega heta hdegree a.1.1
    rcases hdegree a.1.1 with hzero | htwo
    · exact hzero
    · exact False.elim (hnotA htwo)
  · exact doubledAlignedBlackDart_first_step
      homega heta hdegree x

theorem alignedFirstReturn_common_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree false x)).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree true x)).1 := by
  classical
  apply finiteFirstReturn_related_of_aligned_first
    (alignedBoundaryPerm homega heta hdegree false)
    (alignedBoundaryPerm homega heta hdegree true)
    (activeBlackDart (omega := omega) (eta := eta))
    (activeBlackDart (omega := omega) (eta := eta)) (fun a b => a = b)
  · intro a b hab
    subst b
    rfl
  · intro a b hab hnotA hnotB
    subst b
    apply blackBoundary_eq_of_pairing_eq_at
    apply alignedRoutingPairing_eq_layers_at_inactive
      homega heta hdegree a.1.1
    rcases hdegree a.1.1 with hzero | htwo
    · exact hzero
    · exact False.elim (hnotA htwo)
  · exact doubledAlignedBlackDart_first_step
      homega heta hdegree x


end ScratchLocalRetieC
