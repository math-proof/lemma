/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GeographyGame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Digraph.Basic
import Structure.v1.Atlas.TheoryOfComputation.code.GeographyGame


namespace GeographyGame

variable {V : Type*} [DecidableEq V]

/-- `next` is a valid move from `pos` in `G`: there is an edge from the current
vertex to `next`, and `next` has not been visited. -/
def ValidMove (G : Digraph V) (pos : Position V) (next : V) : Prop :=
  G.Adj pos.current next ∧ next ∉ pos.visited

/-- Update a position by moving the token to `next`, marking it visited. -/
def makeMove (pos : Position V) (next : V) : Position V where
  current := next
  visited := pos.visited ∪ {next}

/-- A position is stuck if no valid move exists — the player to move loses. -/
def IsStuck (G : Digraph V) (pos : Position V) : Prop :=
  ∀ v : V, ¬ ValidMove G pos v

end GeographyGame
