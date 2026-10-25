/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/RandomInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
set_option maxHeartbeats 800000

open Finset


namespace RandomInjection

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- A bipartite matching between $X$ and $Y$: a finite set of edges $(x, y)$ in which no two distinct edges share a left endpoint or a right endpoint. -/
structure BipartiteMatching (X Y : Type*) [DecidableEq X] [DecidableEq Y] where
  edges : Finset (X × Y)
  left_injective : ∀ ⦃e₁ e₂⦄, e₁ ∈ edges → e₂ ∈ edges → e₁.1 = e₂.1 → e₁ = e₂
  right_injective : ∀ ⦃e₁ e₂⦄, e₁ ∈ edges → e₂ ∈ edges → e₁.2 = e₂.2 → e₁ = e₂

end RandomInjection
