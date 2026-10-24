/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Expanders

open Finset Function SimpleGraph

namespace HallTheorem

def BipartiteExpander {L R : Type*} [DecidableEq R] [Fintype L]
    (neighbors : L → Finset R) (α β : ℝ) : Prop :=
  ∀ (S : Finset L),
    (S.card : ℝ) ≤ α * (Fintype.card L : ℝ) →
    (β * S.card : ℝ) ≤ ((S.biUnion neighbors).card : ℝ)

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

def RoutingAssignment (N numLayers : ℕ) (α : ℝ) :=
  Fin numLayers → LayerAssignment N α

def uniqueNeighbors {L R : Type*} [DecidableEq L] [DecidableEq R]
    (neighbors : L → Finset R) (S : Finset L) : Finset R :=
  (S.biUnion neighbors).filter fun r => (S.filter fun l => r ∈ neighbors l).card = 1

def rightDegreeInS (S : Finset L) (r : R) : ℕ :=
  (S.filter fun l => G.Adj (Sum.inl l) (Sum.inr r)).card

def uniqueNeighbors (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => G.rightDegreeInS S r = 1

def multiNeighbors (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => G.rightDegreeInS S r ≥ 2

def IsBipartiteOn : Prop :=
  (∀ l₁ l₂ : L, ¬G.Adj (Sum.inl l₁) (Sum.inl l₂)) ∧
  (∀ r₁ r₂ : R, ¬G.Adj (Sum.inr r₁) (Sum.inr r₂))
