/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.Birkhoff
import Instance.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace BipartiteGraph

variable {n : ℕ} (G : BipartiteGraph n)

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
