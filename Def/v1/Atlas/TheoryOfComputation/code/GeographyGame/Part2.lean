/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GeographyGame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Digraph.Basic
import Inductive.v1.Atlas.TheoryOfComputation.code.GeographyGame


namespace GeographyGame

variable {V : Type*} [DecidableEq V]

/-- The initial position of the game starting at vertex `s`, with `s` already visited. -/
def initPosition (s : V) : Position V where
  current := s
  visited := {s}

/-- **Sipser, Lecture 19.** The language
`GG = {⟨G, a⟩ | Player I has a forced win in Generalized Geography on G from a}`.
`GG` is PSPACE-complete. -/
def GG (G : Digraph V) (s : V) : Prop :=
  HasWinningStrategy G (initPosition s) true

end GeographyGame
