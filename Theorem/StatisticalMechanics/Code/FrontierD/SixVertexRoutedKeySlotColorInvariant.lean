/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem FKColoredUnitTransferRoutedKey.ofSlotColorInvariant_splice
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant
      source targetPairing n key hinjective)
    (hTotalC : (fkColoredSlotColorInvariantSplice source targetPairing n
      key hinjective hinvariant).PreservesTotalC)
    (hfalse : (fkColoredSlotColorInvariantSplice source targetPairing n
      key hinjective hinvariant).seamDelta false = 1)
    (htrue : (fkColoredSlotColorInvariantSplice source targetPairing n
      key hinjective hinvariant).seamDelta true = -1) :
    (FKColoredUnitTransferRoutedKey.ofSlotColorInvariant source targetPairing
      n key hinjective hinvariant hTotalC hfalse htrue).splice =
      fkColoredSlotColorInvariantSplice source targetPairing n key
        hinjective hinvariant :=
  rfl


end
end StatMech.FrontierD
