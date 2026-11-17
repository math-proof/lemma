/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Analysis.Convex.Birkhoff
public import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings

@[expose] public section

open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace BipartiteGraph

variable {n : ℕ} (G : BipartiteGraph n)

instance (u : Fin n) (v : Fin n) : Decidable (G.Adj u v) :=
  G.decAdj (u, v)

def leftNeighbors (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (G.Adj u)

def rightNeighbors (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => G.Adj u v)

def denseLeft : Prop :=
  ∀ u : Fin n, n ≤ 2 * (G.leftNeighbors u).card

def denseRight : Prop :=
  ∀ v : Fin n, n ≤ 2 * (G.rightNeighbors v).card

end BipartiteGraph
end Matchings
