/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part8
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp]
theorem withGhost_adj_some_some (x y : V) :
    (withGhost G).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

@[simp]
theorem withGhost_adj_some_ghost (x : V) :
    (withGhost G).Adj (some x) ghost := trivial

@[simp]
theorem withGhost_adj_ghost_some (x : V) :
    (withGhost G).Adj ghost (some x) := trivial


theorem withGhost_ghost_adj (x : V) : (withGhost G).Adj ghost (some x) := trivial


theorem withGhost_restrict (x y : V) :
    (withGhost G).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

end Sharpness
end StatMech
