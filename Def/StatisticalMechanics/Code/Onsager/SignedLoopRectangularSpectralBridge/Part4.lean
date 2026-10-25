/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part3
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

def ons_rectDualDartEquivValid (M N : Nat) :
    (ons_rectDualGraph M N).Dart ≃
      {slot : ons_RectDart M N // ons_rectDartValid M N slot} :=
  Equiv.ofBijective
    (fun dart ↦ ⟨ons_rectDualDartSlot dart,
      ons_rectDualDartSlot_valid dart⟩)
    ⟨fun _ _ h ↦ ons_rectDualDartSlot_injective (congrArg Subtype.val h),
      fun slot ↦ by
        obtain ⟨dart, hdart⟩ :=
          ons_rectDualDartSlot_surjective_valid slot.1 slot.2
        exact ⟨dart, Subtype.ext hdart⟩⟩


def ons_rectDualDartSumEquiv (M N : Nat) :
    (ons_rectDualGraph M N).Dart ⊕
        {slot : ons_RectDart M N // ¬ons_rectDartValid M N slot} ≃
      ons_RectDart M N :=
  (Equiv.sumCongr (ons_rectDualDartEquivValid M N) (Equiv.refl _)).trans
    (Equiv.sumCompl (ons_rectDartValid M N))


noncomputable def ons_rectDualSlotWeight (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (slot : ons_RectDart M N) : Complex :=
  if hslot : ons_rectDartValid M N slot then
    edgeWeight ((ons_rectDualDartEquivValid M N).symm ⟨slot, hslot⟩).edge
  else 0

end
end StatMech.Onsager
