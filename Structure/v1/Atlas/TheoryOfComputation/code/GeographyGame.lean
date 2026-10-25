/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GeographyGame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Digraph.Basic


namespace GeographyGame

variable {V : Type*} [DecidableEq V]

/-- A position in Generalized Geography: the current vertex (whose owner is
about to move) together with the set of already-visited vertices. -/
structure Position (V : Type*) where
  current : V
  visited : Finset V

end GeographyGame
