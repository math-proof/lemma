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
import Instance.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part3
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem doubledAlignedBlackDart_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    Function.Injective
      (doubledAlignedBlackDart homega heta hdegree layer) := by
  intro x y hxy
  apply (doubledAlignedSlotEmbedding
    homega heta hdegree layer).injective
  apply blackDartOfStrandSlot_injective
  exact hxy

theorem doubledAlignedBlackDart_surjective_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    Function.Surjective (fun x : DoubledAlignedState omega eta =>
      (⟨doubledAlignedBlackDart homega heta hdegree layer x,
        by simpa [activeBlackDart, doubledAlignedBlackDart,
            doubledAlignedVertex] using
          sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1⟩ :
        {d : FKMedialBlackDart T //
          activeBlackDart (omega := omega) (eta := eta) d})) := by
  classical
  rintro ⟨d, hd⟩
  let pairing := alignedRoutingLoopPairing homega heta hdegree layer
  let side := strandSlotOfBlackDart pairing d
  have hrange : (d.1.1, side) ∈ Set.range
      (doubledAlignedSlotEmbedding homega heta hdegree layer) :=
    (mem_range_doubledAlignedSlotEmbedding_iff_active
      homega heta hdegree layer d.1.1 side).2 hd
  obtain ⟨x, hx⟩ := hrange
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change (doubledAlignedVertex x,
    doubledAlignedSlot homega heta hdegree layer x) =
      (d.1.1, side) at hx
  change blackDartOfStrandSlot pairing
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x) = d
  rw [hx]
  exact blackDartOfStrandSlot_strandSlotOfBlackDart pairing d

end ScratchLocalRetieC
