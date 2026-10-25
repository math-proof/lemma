/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part4


namespace StatMech.Onsager

open BigOperators

noncomputable def ons_maskedReversibleFactor
    {E : Type*} [DecidableEq E]
    (forbidden : Finset E) (q : E → E → ℂ) : E → E → ℂ :=
  fun x y ↦ if x ∈ forbidden ∨ y ∈ forbidden then 0 else q x y

end StatMech.Onsager
