/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

noncomputable def ons_decTransitionWalk
    (L : ℕ) (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decGraph L).Walk d₁ d₂ := by
  let ext : (ons_decGraph L).Walk d₁ (ons_dartRev L d₁) :=
    .cons (Or.inl rfl) .nil
  let chain₀ := ons_decPortChainPath L d₂.1 (d₁.2 + 2) d₂.2
  have hstart : (d₂.1, d₁.2 + 2) = ons_dartRev L d₁ := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L d₁).symm
    · simp [ons_dartRev]
  let chain : (ons_decGraph L).Walk (ons_dartRev L d₁) d₂ :=
    chain₀.copy hstart rfl
  exact ext.append chain

end StatMech.Onsager
