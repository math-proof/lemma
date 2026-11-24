module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopDecoratedPairColored_slotColor_eq_degreeTwoAligned
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (source : SixVertexLoopDecoratedPair T left right)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1 source.1.2.1)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor (sixVertexLoopDecoratedPairColored source) slot =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource source.1.1.2.1
          source.1.2.2.1 hdegree) slot := by
  rcases slot with ⟨layer, v, side⟩
  cases layer <;> cases side <;> rfl


end
end StatMech.FrontierD
