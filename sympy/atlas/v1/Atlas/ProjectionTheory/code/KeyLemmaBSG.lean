/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/KeyLemmaBSG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset

namespace BSG

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `pathCount₃ A B X a b` is the number of length-3 paths
`a — b₁ — a₁ — b` in the bipartite graph with edge set `X ⊆ A × B`. -/
noncomputable def pathCount₃ (A : Finset α) (B : Finset β) (X : Finset (α × β))
    (a : α) (b : β) : ℕ :=
  ((B ×ˢ A).filter fun (b₁, a₁) =>
    (a, b₁) ∈ X ∧ (a₁, b₁) ∈ X ∧ (a₁, b) ∈ X).card

/-- `pathCount₂ B X a₁ a₂` counts common neighbours in `B` of `a₁` and `a₂`, i.e. the
number of `b ∈ B` with `(a₁, b), (a₂, b) ∈ X` — equivalently $P_2(a_1, a_2)$. -/
noncomputable def pathCount₂ (B : Finset β) (X : Finset (α × β))
    (a₁ a₂ : α) : ℕ :=
  (B.filter fun b => (a₁, b) ∈ X ∧ (a₂, b) ∈ X).card

/-- The *co-neighbours* of `b ∈ B` inside `A`: elements `a ∈ A` with `(a, b) ∈ X`. -/
noncomputable def coNeighbors (X : Finset (α × β)) (b : β) (A : Finset α) : Finset α :=
  A.filter fun a => (a, b) ∈ X

/-- The neighbours of `a ∈ A` inside `B`: elements `b ∈ B` with `(a, b) ∈ X`. -/
noncomputable def neighbors' (X : Finset (α × β)) (a : α) (B : Finset β) : Finset β :=
  B.filter fun b => (a, b) ∈ X

end BSG
