/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice
open Finset


namespace StatMech.FrontierD

noncomputable section

def FKColoredStrandSplice.ofBoundaryInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hboundary : forall x : FKLayeredMedialDart T,
      fkColoredStrandSpliceRawColor source targetPairing slotEquiv
          (x.1, fkMedialBoundaryStep (targetPairing x.1) x.2) =
        fkColoredStrandSpliceRawColor source targetPairing slotEquiv x) :
    FKColoredStrandSplice source where
  targetPairing := targetPairing
  slotEquiv := slotEquiv
  bondCoherent :=
    (fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant
      source targetPairing slotEquiv).2 hboundary

def FKColoredStrandSlotColorEquiv
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) : Prop :=
  forall slot,
    fkColoredLayeredSlotColor source (slotEquiv slot) =
      fkColoredLayeredSlotColor target slot

def fkColoredTrueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) : Nat :=
  Fintype.card {slot : FKLayeredStrandSlot T //
    fkColoredLayeredSlotColor source slot = true}

noncomputable def boolFalseFiberEquivComplementTrue
    {A : Type*} [Fintype A] (color : A -> Bool) :
    {x : A // color x = false} ≃ {x : A // ¬ color x = true} :=
  Equiv.subtypeEquiv (Equiv.refl A) fun x => by
    generalize hcolor : color x = value
    cases value <;> simp [hcolor]

end
end StatMech.FrontierD
