/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredBlackDartStrandSlot_injective
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    Function.Injective (fkColoredBlackDartStrandSlot pairing) := by
  intro first second h
  rcases first with ⟨⟨v, firstSide⟩, hfirst⟩
  rcases second with ⟨⟨w, secondSide⟩, hsecond⟩
  apply Subtype.ext
  have hvw : v = w := congrArg Prod.fst h
  subst w
  apply Prod.ext
  · rfl
  · have hslot := congrArg Prod.snd h
    cases hp : pairing v <;>
      cases hv : fkMedialVertexParity v <;>
      cases firstSide <;> cases secondSide <;>
      simp [fkMedialCheckerColor, fkMedialSideVertical,
        fkColoredBlackDartStrandSlot, fkColoredSideSlot,
        hp, hv] at hfirst hsecond hslot ⊢


end
end StatMech.FrontierD
