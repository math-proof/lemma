module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part14
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

end ScratchLocalRetieC
