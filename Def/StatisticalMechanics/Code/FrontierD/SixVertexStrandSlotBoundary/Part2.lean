/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkColoredBlackDartStrandSlotEquiv
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    FKMedialBlackDart T ≃ T.Vertex × Bool :=
  Equiv.ofBijective (fkColoredBlackDartStrandSlot pairing) (by
    apply (Fintype.bijective_iff_injective_and_card
      (fkColoredBlackDartStrandSlot pairing)).2
    refine ⟨fkColoredBlackDartStrandSlot_injective pairing, ?_⟩
    rw [card_fkMedialBlackDart]
    simp [EvenTorus.Vertex]
    ring)

end
end StatMech.FrontierD
