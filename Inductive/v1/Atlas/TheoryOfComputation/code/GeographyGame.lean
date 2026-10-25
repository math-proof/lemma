/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GeographyGame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Digraph.Basic
import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame


namespace GeographyGame

variable {V : Type*} [DecidableEq V]

/-- The "has winning strategy" relation for Generalized Geography. `HasWinningStrategy G pos b`
holds when the player whose turn it is (`b = true` for Player I, `b = false` for Player II)
has a strategy to win from position `pos`:
- Player I (`true`) wins by choosing some valid move leading to a position where Player II loses.
- Player II (`false`) wins immediately if the position is stuck (Player I cannot move), or if
  every valid move by Player I leads to a Player-I-winning position. -/
inductive HasWinningStrategy (G : Digraph V) : Position V → Bool → Prop where
  | playerI_moves {pos : Position V} {next : V}
    (hmove : ValidMove G pos next)
    (hwin : HasWinningStrategy G (makeMove pos next) false) :
    HasWinningStrategy G pos true
  | playerII_stuck {pos : Position V}
    (hstuck : IsStuck G pos) :
    HasWinningStrategy G pos false
  | playerII_moves {pos : Position V}
    (hnotStuck : ¬ IsStuck G pos)
    (hwin : ∀ next : V, ValidMove G pos next →
      HasWinningStrategy G (makeMove pos next) true) :
    HasWinningStrategy G pos false

end GeographyGame
