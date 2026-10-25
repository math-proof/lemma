/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open Finset Function


namespace NonnegDependence

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- A bipartite matching between $X$ and $Y$: a finite set of edges $(x, y)$ such that no two edges share a left endpoint or a right endpoint. -/
structure Matching (X Y : Type*) [DecidableEq X] [DecidableEq Y] where
  edges : Finset (X × Y)
  left_inj : ∀ ⦃e₁ e₂⦄, e₁ ∈ edges → e₂ ∈ edges → e₁.1 = e₂.1 → e₁ = e₂
  right_inj : ∀ ⦃e₁ e₂⦄, e₁ ∈ edges → e₂ ∈ edges → e₁.2 = e₂.2 → e₁ = e₂

end NonnegDependence
