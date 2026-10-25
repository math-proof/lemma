/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamilton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace TournamentHamilton

/-- A tournament on an arbitrary vertex type $V$: an irreflexive, asymmetric, and complete
Boolean edge relation (between distinct vertices exactly one direction holds). -/
structure Tournament (V : Type*) where
  edge : V → V → Bool
  edge_irrefl : ∀ v, edge v v = false
  edge_complete : ∀ u v, u ≠ v → (edge u v = true ∨ edge v u = true)
  edge_asymm : ∀ u v, edge u v = true → edge v u = false

end TournamentHamilton
