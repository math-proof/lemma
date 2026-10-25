/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Def.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part4


namespace StatMech.Onsager

open BigOperators

theorem ons_mask_stateWeightedReversibleTurnMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    (forbidden : Finset E)
    (dir : E → Fin 4) (omega : ℂ)
    (rowWeight colWeight : E → ℂ) (q : E → E → ℂ) :
    ons_maskMatrix forbidden
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) =
      ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight
        (ons_maskedReversibleFactor forbidden q) := by
  ext x y
  simp only [ons_maskMatrix, ons_stateWeightedReversibleTurnMatrix,
    ons_maskedReversibleFactor]
  split <;> ring

theorem ons_maskedReversibleFactor_rev
    {E : Type*} [DecidableEq E]
    (rev : E → E) (forbidden : Finset E)
    (hforbidden : ∀ x, rev x ∈ forbidden ↔ x ∈ forbidden)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (x y : E) :
    ons_maskedReversibleFactor forbidden q (rev y) (rev x) =
      ons_maskedReversibleFactor forbidden q x y := by
  unfold ons_maskedReversibleFactor
  simp only [hforbidden y, hforbidden x]
  by_cases h : x ∈ forbidden ∨ y ∈ forbidden
  · have h' : y ∈ forbidden ∨ x ∈ forbidden := h.elim Or.inr Or.inl
    rw [if_pos h, if_pos h']
  · have h' : ¬ (y ∈ forbidden ∨ x ∈ forbidden) := by tauto
    rw [if_neg h, if_neg h', hq]

end StatMech.Onsager
