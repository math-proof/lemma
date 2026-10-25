/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

def FKColoredStrandSplice.ofColorEquiv
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv) :
    FKColoredStrandSplice source where
  targetPairing := fun layer => (target layer).pairing
  slotEquiv := slotEquiv
  bondCoherent := by
    intro x
    rw [fkColoredStrandSpliceRawColor_eq_of_colorEquiv
        source target slotEquiv hcolor,
      fkColoredStrandSpliceRawColor_eq_of_colorEquiv
        source target slotEquiv hcolor]
    rcases x with ⟨layer, d⟩
    exact (target layer).color_bondMate d

def FKColoredStrandSplice.target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    FKColoredLoopPairingPair T := fun layer =>
  { pairing := splice.targetPairing layer
    color := fun d => fkColoredStrandSpliceRawColor source
      splice.targetPairing splice.slotEquiv (layer, d)
    color_localMate := fkColoredStrandSpliceRawColor_localMate
      source splice.targetPairing splice.slotEquiv layer
    color_bondMate := by
      intro d
      exact splice.bondCoherent (layer, d) }

end
end StatMech.FrontierD
