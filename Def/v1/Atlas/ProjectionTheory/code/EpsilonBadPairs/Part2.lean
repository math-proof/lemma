/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/EpsilonBadPairs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.ProjectionTheory.code.EpsilonBadPairs


namespace BSG

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The bad-pairs counting function `BP_ε(b) = #{(a₁, a₂) ∈ N(b)² : (a₁, a₂) is ε-bad}`
from the BSG analysis. -/
noncomputable def badPairsCount (X : Finset (α × β)) (K ε : ℝ) (b : β) : ℕ :=
  ((neighborhood X b) ×ˢ (neighborhood X b)).filter
    (fun (p : α × α) => IsEpsilonBad X K ε p.1 p.2) |>.card

end BSG
