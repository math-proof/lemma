/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Field
import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
import Theorem.v1.Atlas.BooleanFunctions.code.MISBound
import Structure.v1.Atlas.BooleanFunctions.code.UniqueGames.Part2


namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

def NonBipartiteUniqueGame.edgesWithin (game : NonBipartiteUniqueGame X k)
    (X' : Finset X) : Finset (X × X) :=
  game.edges.filter (fun e => e.1 ∈ X' ∧ e.2 ∈ X')

def NonBipartiteUniqueGame.edgeSatisfiedBy (game : NonBipartiteUniqueGame X k)
    (A : X → Fin k) (e : X × X) : Prop :=
  game.constraint e.1 e.2 (A e.1) = A e.2

end UniqueGames
