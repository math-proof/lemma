/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}


def bc16_IsSeparator (G : SimpleGraph V) (S T : Set V) (C : Set V) : Prop :=
  ∀ ⦃s : V⦄, s ∈ S → ∀ ⦃t : V⦄, t ∈ T → ∀ p : G.Walk s t, ∃ c ∈ C, c ∈ p.support


end StatMech.Walls
