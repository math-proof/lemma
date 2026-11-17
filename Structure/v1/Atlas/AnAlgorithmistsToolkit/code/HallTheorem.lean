/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hall
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders.Part2
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Expanders
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HallTheorem
public section

open Finset Function SimpleGraph


namespace HallTheorem

structure MultibutterflyNetwork (N : ℕ) (numLayers : ℕ) where
  α : ℝ
  β : ℝ
  hβ : 1 < β
  upNeighbors : Fin numLayers → (Fin N → Finset (Fin N))
  downNeighbors : Fin numLayers → (Fin N → Finset (Fin N))
  upIsExpander : ∀ i, BipartiteExpander (upNeighbors i) α β
  downIsExpander : ∀ i, BipartiteExpander (downNeighbors i) α β

structure LayerAssignment (N : ℕ) (α : ℝ) where
  up : Finset (Fin N)
  down : Finset (Fin N)
  disjoint : Disjoint up down
  up_small : (up.card : ℝ) ≤ α * N
  down_small : (down.card : ℝ) ≤ α * N

end HallTheorem
