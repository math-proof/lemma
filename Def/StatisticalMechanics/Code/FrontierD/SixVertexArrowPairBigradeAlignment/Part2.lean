/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexArrowPairBigradeAlignment


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexArrowTrueStrandSlotEquiv
    {T : EvenTorus} (omega : SixVertexArrows T) :
    {slot : T.Vertex × Bool //
        sixVertexArrowStrandSlotColor omega slot = true} ≃
      ({v : T.Vertex //
          omega.horizontal v = fkMedialVertexParity v} × Bool) where
  toFun slot := by
    rcases slot with ⟨⟨v, side⟩, hcolor⟩
    cases side
    · let u : T.Vertex :=
        (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)
      refine (⟨u, ?_⟩, false)
      apply (sixVertexArrowStrandSlotColor_east_eq_true_iff omega u).mp
      rw [← sixVertexArrowStrandSlotColor_west_eq_east_pred omega v]
      exact hcolor
    · refine (⟨v, ?_⟩, true)
      exact (sixVertexArrowStrandSlotColor_east_eq_true_iff omega v).mp hcolor
  invFun slot := by
    rcases slot with ⟨⟨v, hv⟩, side⟩
    cases side
    · refine ⟨((finitePeriodicSucc T.width_pos v.1, v.2), false), ?_⟩
      rw [sixVertexArrowStrandSlotColor_west_succ_eq_east]
      exact (sixVertexArrowStrandSlotColor_east_eq_true_iff omega v).mpr hv
    · exact ⟨(v, true),
        (sixVertexArrowStrandSlotColor_east_eq_true_iff omega v).mpr hv⟩
  left_inv slot := by
    rcases slot with ⟨⟨v, side⟩, hcolor⟩
    cases side
    · apply Subtype.ext
      simp [finitePeriodicSucc_cyclicPred]
    · rfl
  right_inv slot := by
    rcases slot with ⟨⟨v, hv⟩, side⟩
    cases side
    · apply Prod.ext
      · apply Subtype.ext
        simp [svCyclicPred_finitePeriodicSucc]
      · rfl
    · rfl

def sixVertexArrowTrueStrandSlotCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  Fintype.card {slot : T.Vertex × Bool //
    sixVertexArrowStrandSlotColor omega slot = true}

end
end StatMech.FrontierD
