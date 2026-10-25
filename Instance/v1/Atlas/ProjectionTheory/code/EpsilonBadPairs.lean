/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/EpsilonBadPairs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.EpsilonBadPairs


namespace BSG

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Decidability of the `ε`-bad predicate (used to define the badness counting function
below). -/
noncomputable instance instDecidableIsEpsilonBad (X : Finset (α × β)) (K ε : ℝ) (a₁ a₂ : α) :
    Decidable (IsEpsilonBad X K ε a₁ a₂) :=
  inferInstanceAs (Decidable (_ < _))

end BSG
