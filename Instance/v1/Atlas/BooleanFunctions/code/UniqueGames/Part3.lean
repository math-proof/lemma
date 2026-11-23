/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
public import Theorem.v1.Atlas.BooleanFunctions.code.MISBound
public import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part4
@[expose] public section

namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

instance (game : NonBipartiteUniqueGame X k) (A : X → Finset (Fin k)) (e : X × X) :
    Decidable (game.edgeTSatisfiedBy A e) :=
  inferInstanceAs (Decidable (∃ a ∈ A e.1, ∃ b ∈ A e.2, game.constraint e.1 e.2 a = b))

end UniqueGames
