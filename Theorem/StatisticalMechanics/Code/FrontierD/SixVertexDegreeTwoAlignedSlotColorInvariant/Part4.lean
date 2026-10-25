/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkMedialBlackDartSwap_self_vertex {T : EvenTorus}
    (dart : FKMedialBlackDart T) :
    (fkMedialBlackDartSwap dart.1.1 dart).1.1 = dart.1.1 := by
  let pairing : FKMedialLoopPairing T := fun _ => false
  have hcoordinate := fkColoredBlackDartStrandSlot_blackSwap
    pairing dart.1.1 dart
  have hfst := congrArg Prod.fst hcoordinate
  change (fkMedialBlackDartSwap dart.1.1 dart).1.1 =
    (fkColoredVertexStrandSlotSwap dart.1.1
      (fkColoredBlackDartStrandSlotEquiv pairing dart)).1 at hfst
  have hswapFst : (fkColoredVertexStrandSlotSwap dart.1.1
      (fkColoredBlackDartStrandSlotEquiv pairing dart)).1 =
      (fkColoredBlackDartStrandSlotEquiv pairing dart).1 := by
    rcases dart with ⟨⟨v, side⟩, hdart⟩
    cases hv : fkMedialVertexParity v <;> cases side <;>
      simp [fkColoredVertexStrandSlotSwap,
        fkColoredBlackDartStrandSlotEquiv_apply,
        fkColoredBlackDartStrandSlot, fkColoredSideSlot,
        fkMedialCheckerColor, fkMedialSideVertical, pairing, hv] at hdart ⊢
  rw [hswapFst] at hfst
  exact hfst

end
end StatMech.FrontierD
