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
public import Structure.v1.Atlas.BooleanFunctions.code.UniqueGames.Part2

@[expose] public section

namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

def NonBipartiteUniqueGame.edgesWithin (game : NonBipartiteUniqueGame X k)
    (X' : Finset X) : Finset (X × X) :=
  game.edges.filter (fun e => e.1 ∈ X' ∧ e.2 ∈ X')

def NonBipartiteUniqueGame.edgeSatisfiedBy (game : NonBipartiteUniqueGame X k)
    (A : X → Fin k) (e : X × X) : Prop :=
  game.constraint e.1 e.2 (A e.1) = A e.2

end UniqueGames
