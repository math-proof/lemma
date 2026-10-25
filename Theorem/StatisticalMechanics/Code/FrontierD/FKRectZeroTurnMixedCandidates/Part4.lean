/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part4
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnMixedTouchedCrossings_eq_primal
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectZeroTurnMixedTouchedCrossings R omega C =
      fkRectZeroTurnPrimalTouchedCrossingsInMixed R omega C := by
  classical
  unfold FKRectZeroTurnUsesPrimalTouchedCrossings at hC
  unfold fkRectZeroTurnMixedTouchedCrossings
  dsimp only
  rw [dif_pos hC]

theorem fkRectZeroTurnMixedTouchedCrossings_eq_dual
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectZeroTurnMixedTouchedCrossings R omega C =
      fkRectZeroTurnDualTouchedCrossingsInMixed R omega C := by
  classical
  unfold FKRectZeroTurnUsesPrimalTouchedCrossings at hC
  unfold fkRectZeroTurnMixedTouchedCrossings
  dsimp only
  rw [dif_neg hC]

theorem mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Sum.inl X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C ↔
      FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ∧
        X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C := by
  classical
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_primal R omega C hC]
    simp [fkRectZeroTurnPrimalTouchedCrossingsInMixed, hC]
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_dual R omega C hC]
    simp [fkRectZeroTurnDualTouchedCrossingsInMixed, hC]

theorem mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawWiredDualHorizontalCrossingComponent R omega) :
    Sum.inr X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C ↔
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ∧
        X ∈ fkRectZeroTurnDualTouchedCrossings R omega C := by
  classical
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_primal R omega C hC]
    simp [fkRectZeroTurnPrimalTouchedCrossingsInMixed, hC]
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_dual R omega C hC]
    simp [fkRectZeroTurnDualTouchedCrossingsInMixed, hC]


theorem fkRectZeroTurnMixedTouchedCrossings_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectZeroTurnMixedTouchedCrossings R omega C).Nonempty := by
  classical
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  change (if h : FKRectWalkAvoidsRowSeam R p then
      fkRectZeroTurnPrimalTouchedCrossingsInMixed R omega C
    else
      fkRectZeroTurnDualTouchedCrossingsInMixed R omega C).Nonempty
  split
  · obtain ⟨X, hX⟩ :=
      fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
        R omega C (by assumption)
    exact ⟨Sum.inl X, by
      simp [fkRectZeroTurnPrimalTouchedCrossingsInMixed, hX]⟩
  · obtain ⟨X, hX⟩ :=
      fkRectZeroTurnDualTouchedCrossings_nonempty R omega C
    exact ⟨Sum.inr X, by
      simp [fkRectZeroTurnDualTouchedCrossingsInMixed, hX]⟩


end
end StatMech.FrontierD
