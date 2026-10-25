/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part17
open StatMech.FrontierD


namespace StatMech.FrontierD

noncomputable def doubledAlignedBlackDartEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    DoubledAlignedState omega eta ≃
      {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} :=
  Equiv.ofBijective
    (fun x =>
      (⟨doubledAlignedBlackDart homega heta hdegree layer x,
        by simpa [activeBlackDart, doubledAlignedBlackDart,
            doubledAlignedVertex] using
          sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1⟩ :
        {d : FKMedialBlackDart T //
          activeBlackDart (omega := omega) (eta := eta) d}))
    ⟨fun x y h => doubledAlignedBlackDart_injective
        homega heta hdegree layer (congrArg Subtype.val h),
      doubledAlignedBlackDart_surjective_active
        homega heta hdegree layer⟩

noncomputable def alignedBoundaryPerm
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) : Equiv.Perm (FKMedialBlackDart T) :=
  fkMedialBlackBoundaryPerm
    (alignedRoutingLoopPairing homega heta hdegree layer)

end StatMech.FrontierD
