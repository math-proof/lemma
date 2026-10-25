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
import Instance.v1.Atlas.BooleanFunctions.code.UniqueGames.Part2


namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

noncomputable def NonBipartiteUniqueGame.fractionSatisfiedWithin
    (game : NonBipartiteUniqueGame X k) (X' : Finset X) (A : X → Fin k) : ℝ :=
  ((game.edgesWithin X').filter (fun e => game.edgeSatisfiedBy A e)).card /
    (game.edgesWithin X').card

def NonBipartiteUniqueGame.edgeTSatisfiedBy (game : NonBipartiteUniqueGame X k)
    (A : X → Finset (Fin k)) (e : X × X) : Prop :=
  ∃ a ∈ A e.1, ∃ b ∈ A e.2, game.constraint e.1 e.2 a = b

end UniqueGames
