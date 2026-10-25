/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


theorem shb_P2_support_of_complementResummation
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {x z u : V}
    (p₁₂ : G.Path x z) (p₁ : G.Path x u) (p₂ : H.Path u z)
    (hresum : shb_P2ComplementResummation G H β J p₁₂ p₁ p₂) :
    shb_rhoSupport G β J x z p₁₂ =
      shb_rhoSupport G β J x u p₁ * shb_rhoSupport H β J u z p₂ := by
  have hZG : currentSum G β J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G β J)
  have hZH : currentSum H β J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos H β J)
  unfold shb_P2ComplementResummation at hresum
  unfold shb_rhoSupport
  field_simp [hZG, hZH]
  exact hresum

end StatMech.Sharpness
